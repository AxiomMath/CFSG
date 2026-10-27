module

public import CFSG.Quasithin.EmptyFaithful.S151YF
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {G : Type} [Group G]

structure Ya7Core (L S : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7))
    (P : Finset (Finset (Fin 7))) : Prop where
  surj : Function.Surjective α
  ker : α.ker = CFSG.Open.pCore 2 ↥L
  sylow : IsSylowTwoOf (S ⊓ L) L
  two : IsPGroup 2 ↥S
  norm : S ≤ Subgroup.normalizer (L : Set G)
  part : IsPartitionOfType P {2, 2, 2, 1}
  stab : ∀ x : ↥L, (x : G) ∈ S → StabilizesPartition (α x : Equiv.Perm (Fin 7)) P

@[expose] def ya7D (L S : Subgroup G) (α : ↥L →* alternatingGroup (Fin 7)) :
    Subgroup (alternatingGroup (Fin 7)) :=
  ((S ⊓ L).subgroupOf L).map α

theorem mem_ya7D {L S : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
    {d : alternatingGroup (Fin 7)} :
    d ∈ ya7D L S α ↔ ∃ x : ↥L, (x : G) ∈ S ∧ α x = d := by
  unfold ya7D
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Subgroup.mem_subgroupOf.mp hx).1, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr ⟨hx, x.2⟩, rfl⟩

variable {L S : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)} {P : Finset (Finset (Fin 7))}

theorem Ya7Core.sylowD (hc : Ya7Core L S α P) : IsSylowTwoOf (ya7D L S α) ⊤ := by
  have h := ya7_isSylowTwoOf_map α hc.sylow
  rwa [MonoidHom.range_eq_top.mpr hc.surj] at h

theorem Ya7Core.stabD (hc : Ya7Core L S α P) :
    ∀ d ∈ ya7D L S α, StabilizesPartition (d : Equiv.Perm (Fin 7)) P := by
  intro d hd
  obtain ⟨x, hx, rfl⟩ := mem_ya7D.mp hd
  exact hc.stab x hx

theorem ya7_stab_one (P : Finset (Finset (Fin 7))) :
    StabilizesPartition ((1 : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) P :=
  (ya7PartStab P).one_mem

theorem mem_pCoreOf_iff_ker (hker : α.ker = CFSG.Open.pCore 2 ↥L) {x : G} :
    x ∈ pCoreOf 2 L ↔ ∃ hx : x ∈ L, α ⟨x, hx⟩ = 1 := by
  unfold pCoreOf
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have : y ∈ α.ker := by rw [hker]; exact hy
    exact this
  · rintro ⟨hx, h1⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [← hker]
    exact h1

theorem Ya7Core.pCoreOf_le_pre (hc : Ya7Core L S α P) : pCoreOf 2 L ≤ ya7Pre L α P := by
  intro x hx
  obtain ⟨hxL, h1⟩ := (mem_pCoreOf_iff_ker hc.ker).mp hx
  refine mem_ya7Pre.mpr ⟨hxL, ?_⟩
  rw [h1]
  exact ya7_stab_one P

theorem Ya7Core.pCoreOf_le_sylow (hc : Ya7Core L S α P) : pCoreOf 2 L ≤ S ⊓ L :=
  hc.sylow.pCoreOf_le

theorem Ya7Core.inf_le_pre (hc : Ya7Core L S α P) : S ⊓ L ≤ ya7Pre L α P := fun x hx =>
  mem_ya7Pre.mpr ⟨hx.2, hc.stab ⟨x, hx.2⟩ hx.1⟩

theorem ya7_exists_perm {s : G} (hs : s ∈ Subgroup.normalizer (L : Set G))
    (hsurj : Function.Surjective α) (hker : α.ker = CFSG.Open.pCore 2 ↥L) :
    ∃ π : Equiv.Perm (Fin 7), ∀ x y : ↥L, (y : G) = s * x * s⁻¹ →
      (α y : Equiv.Perm (Fin 7)) = π * (α x : Equiv.Perm (Fin 7)) * π⁻¹ := by
  classical
  let φ : MulAut ↥L := L.normalizerMonoidHom ⟨s, hs⟩
  have hφ : ∀ x : ↥L, ((φ x : ↥L) : G) = s * x * s⁻¹ := fun x =>
    L.normalizerMonoidHom_apply_apply_coe ⟨s, hs⟩ x
  have hpc : ∀ x : ↥L, φ x ∈ CFSG.Open.pCore 2 ↥L ↔ x ∈ CFSG.Open.pCore 2 ↥L := by
    have hchar : (CFSG.Open.pCore 2 ↥L).Characteristic :=
      CFSG.LieType.BorelTits.pCore_characteristic 2
    have h1 : (CFSG.Open.pCore 2 ↥L).map φ.toMonoidHom = CFSG.Open.pCore 2 ↥L :=
      Subgroup.characteristic_iff_map_eq.mp hchar φ
    intro x
    constructor
    · intro hx
      rw [← h1] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have : y = x := φ.injective hyx
      rw [← this]
      exact hy
    · intro hx
      rw [← h1]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hker' : α.ker ≤ (α.comp φ.toMonoidHom).ker := by
    intro x hx
    have hx' : x ∈ CFSG.Open.pCore 2 ↥L := by rw [← hker]; exact hx
    have h2 : φ x ∈ α.ker := by rw [hker]; exact (hpc x).mpr hx'
    exact h2
  let θ : alternatingGroup (Fin 7) →* alternatingGroup (Fin 7) :=
    α.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
      ⟨α.comp φ.toMonoidHom, hker'⟩
  have hθ : ∀ x : ↥L, θ (α x) = α (φ x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply α _ _ ⟨α.comp φ.toMonoidHom, hker'⟩ x
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨x, rfl⟩ := hsurj a
    rw [hθ] at ha
    have h1 : φ x ∈ CFSG.Open.pCore 2 ↥L := by rw [← hker]; exact ha
    have h2 : x ∈ CFSG.Open.pCore 2 ↥L := (hpc x).mp h1
    rw [← hker] at h2
    exact h2
  have hθsurj : Function.Surjective θ := by
    intro b
    obtain ⟨y, rfl⟩ := hsurj b
    obtain ⟨x, hx⟩ := φ.surjective y
    exact ⟨α x, by rw [hθ, hx]⟩
  let e : MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 e
  refine ⟨π, fun x y hxy => ?_⟩
  have hyφ : y = φ x := Subtype.ext (by rw [hφ x, hxy])
  have h1 : α y = e (α x) := by rw [hyφ, ← hθ]; rfl
  have h2 := congrArg (fun f : MulAut (alternatingGroup (Fin 7)) =>
    ((f (α x) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) hπ
  simp only [MulAut.conjNormal_apply] at h2
  rw [h1]
  exact h2.symm

theorem Ya7Core.S_le_normalizer (hc : Ya7Core L S α P) :
    S ≤ Subgroup.normalizer (ya7Pre L α P : Set G) := by
  obtain ⟨-, -, -, -, huniq, -, -⟩ := ya7_data (ya7D L S α) hc.sylowD hc.part hc.stabD
  have key : ∀ s ∈ S, ∀ z : G, z ∈ ya7Pre L α P → s * z * s⁻¹ ∈ ya7Pre L α P := by
    intro s hs z hz
    obtain ⟨π, hπ⟩ := ya7_exists_perm (hc.norm hs) hc.surj hc.ker
    have hP'stab : ∀ d ∈ ya7D L S α, StabilizesPartition (d : Equiv.Perm (Fin 7)) (ya7Rel π P) := by
      intro d hd
      obtain ⟨w, hwS, rfl⟩ := mem_ya7D.mp hd
      have hx : s⁻¹ * (w : G) * s ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hc.norm hs)) (w : G)).mp w.2
        simpa using this
      have hxS : s⁻¹ * (w : G) * s ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs) hwS) hs
      have h1 := hπ ⟨s⁻¹ * (w : G) * s, hx⟩ w (by simp [mul_assoc])
      have h2 := ya7_stab_conj π (hc.stab ⟨s⁻¹ * (w : G) * s, hx⟩ hxS)
      rw [← h1] at h2
      exact h2
    have heq : ya7Rel π P = P := huniq _ (ya7Rel_type hc.part π) hP'stab
    obtain ⟨hzL, hzs⟩ := mem_ya7Pre.mp hz
    have hszL : s * z * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hc.norm hs) z).mp hzL
    refine mem_ya7Pre.mpr ⟨hszL, ?_⟩
    have h1 := hπ ⟨z, hzL⟩ ⟨s * z * s⁻¹, hszL⟩ rfl
    rw [h1]
    have h2 : StabilizesPartition (π * (α ⟨z, hzL⟩ : Equiv.Perm (Fin 7)) * π⁻¹) (ya7Rel π P) :=
      ya7_stab_conj π hzs
    rwa [heq] at h2
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact key s hs z
  · intro hz
    have := key s⁻¹ (S.inv_mem hs) _ hz
    simpa [mul_assoc] using this

theorem ya7_pow_mul_mem {N : Subgroup G} {s p : G} (hs : s ∈ Subgroup.normalizer (N : Set G))
    (hp : p ∈ N) (n : ℕ) : ∃ q ∈ N, (s * p) ^ n = s ^ n * q := by
  induction n with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq, hqe⟩ := ih
    refine ⟨s⁻¹ * q * s * p, ?_, ?_⟩
    · have h1 : s⁻¹ * q * s ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hs) q).mp hq
        simpa using this
      exact N.mul_mem h1 hp
    · rw [pow_succ, hqe, pow_succ]
      group

theorem Ya7Core.mem_sup (hc : Ya7Core L S α P) {x : G} (hx : x ∈ ya7Pre L α P ⊔ S) :
    ∃ s ∈ S, ∃ p ∈ ya7Pre L α P, x = s * p := by
  have h : ((S ⊔ ya7Pre L α P : Subgroup G) : Set G) = (S : Set G) * (ya7Pre L α P : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right S (ya7Pre L α P) hc.S_le_normalizer
  rw [sup_comm] at hx
  have hx' : x ∈ ((S ⊔ ya7Pre L α P : Subgroup G) : Set G) := hx
  rw [h] at hx'
  obtain ⟨s, hs, p, hp, rfl⟩ := hx'
  exact ⟨s, hs, p, hp, rfl⟩

theorem Ya7Core.H_le_normalizer (hc : Ya7Core L S α P) :
    ya7Pre L α P ⊔ S ≤ Subgroup.normalizer (ya7Pre L α P : Set G) :=
  sup_le Subgroup.le_normalizer hc.S_le_normalizer

theorem Ya7Core.two_pow (hc : Ya7Core L S α P) :
    ∀ x ∈ ya7Pre L α P ⊔ S, ∃ k : ℕ, x ^ 2 ^ k ∈ ya7Pre L α P := by
  intro x hx
  obtain ⟨s, hs, p, hp, rfl⟩ := hc.mem_sup hx
  obtain ⟨k, hk⟩ := hc.two ⟨s, hs⟩
  refine ⟨k, ?_⟩
  obtain ⟨q, hq, hqe⟩ := ya7_pow_mul_mem (hc.S_le_normalizer hs) hp (2 ^ k)
  have hsk : s ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [hqe, hsk, one_mul]
  exact hq

theorem Ya7Core.inv_mul_mem_pCoreOf (hc : Ya7Core L S α P) {x : ↥L} {z : G} (hz : z ∈ L)
    (h : α x = α ⟨z, hz⟩) : (x : G)⁻¹ * z ∈ pCoreOf 2 L := by
  have hmem : (x : G)⁻¹ * z ∈ L := L.mul_mem (L.inv_mem x.2) hz
  refine (mem_pCoreOf_iff_ker hc.ker).mpr ⟨hmem, ?_⟩
  have : α ⟨(x : G)⁻¹ * z, hmem⟩ = (α x)⁻¹ * α ⟨z, hz⟩ := by
    rw [← map_inv, ← map_mul]
    rfl
  rw [this, h]
  exact inv_mul_cancel _

theorem Ya7Core.S_maximal (hc : Ya7Core L S α P) {K : Subgroup G} (hSK : S ≤ K)
    (hKH : K ≤ ya7Pre L α P ⊔ S) : K = S ∨ K = ya7Pre L α P ⊔ S := by
  obtain ⟨-, -, hbet, -, -, -, -⟩ := ya7_data (ya7D L S α) hc.sylowD hc.part hc.stabD
  have hKdecomp : ∀ k ∈ K, ∃ s ∈ S, ∃ p ∈ K ⊓ ya7Pre L α P, k = s * p := by
    intro k hk
    obtain ⟨s, hs, p, hp, rfl⟩ := hc.mem_sup (hKH hk)
    refine ⟨s, hs, p, ⟨?_, hp⟩, rfl⟩
    have := K.mul_mem (K.inv_mem (hSK hs)) hk
    simpa using this
  have hK₀L : K ⊓ ya7Pre L α P ≤ L := fun x hx => ya7Pre_le L α P hx.2
  set A : Subgroup (alternatingGroup (Fin 7)) := ((K ⊓ ya7Pre L α P).subgroupOf L).map α with hA
  have hDA : ya7D L S α ≤ A := by
    intro d hd
    obtain ⟨x, hxS, rfl⟩ := mem_ya7D.mp hd
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr
      ⟨hSK hxS, hc.inf_le_pre ⟨hxS, x.2⟩⟩, rfl⟩
  have hAQ : A ≤ ya7PartStab P := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    exact (mem_ya7Pre.mp (Subgroup.mem_subgroupOf.mp hx).2).2
  rcases hbet A hDA hAQ with hAD | hAQ'
  · left
    refine le_antisymm (fun k hk => ?_) hSK
    obtain ⟨s, hs, p, hp, rfl⟩ := hKdecomp k hk
    refine S.mul_mem hs ?_
    have hpA : α ⟨p, hK₀L hp⟩ ∈ ya7D L S α := by
      rw [← hAD]
      exact Subgroup.mem_map.mpr ⟨⟨p, hK₀L hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
    obtain ⟨x, hxS, hx⟩ := mem_ya7D.mp hpA
    have hker := hc.inv_mul_mem_pCoreOf (hK₀L hp) hx
    have hRS : (x : G)⁻¹ * p ∈ S := (hc.pCoreOf_le_sylow hker).1
    have : p = (x : G) * ((x : G)⁻¹ * p) := by group
    rw [this]
    exact S.mul_mem hxS hRS
  · right
    refine le_antisymm hKH (sup_le (fun z hz => ?_) hSK)
    obtain ⟨hzL, hzst⟩ := mem_ya7Pre.mp hz
    have hzQ : α ⟨z, hzL⟩ ∈ A := by
      rw [hAQ']
      exact hzst
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hzQ
    have hxK : (x : G) ∈ K := (Subgroup.mem_subgroupOf.mp hx).1
    have hker := hc.inv_mul_mem_pCoreOf hzL hxz
    have hRK : (x : G)⁻¹ * z ∈ K := hSK (hc.pCoreOf_le_sylow hker).1
    have : z = (x : G) * ((x : G)⁻¹ * z) := by group
    rw [this]
    exact K.mul_mem hxK hRK

theorem Ya7Core.S_not_normal (hc : Ya7Core L S α P) :
    ¬ (ya7Pre L α P ⊔ S ≤ Subgroup.normalizer (S : Set G)) := by
  obtain ⟨-, -, -, ⟨q, hq, d, hd, hnot⟩, -, -, -⟩ :=
    ya7_data (ya7D L S α) hc.sylowD hc.part hc.stabD
  intro hN
  apply hnot
  obtain ⟨w, hwS, rfl⟩ := mem_ya7D.mp hd
  obtain ⟨z, hz⟩ := hc.surj q
  have hzPt : (z : G) ∈ ya7Pre L α P :=
    mem_ya7Pre.mpr ⟨z.2, by
      show StabilizesPartition ((α z : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) P
      rw [hz]
      exact hq⟩
  have hzN := hN (Subgroup.mem_sup_left hzPt)
  have hconj : (z : G) * (w : G) * (z : G)⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp hzN (w : G)).mp hwS
  rw [← hz]
  exact mem_ya7D.mpr ⟨z * w * z⁻¹, hconj, by simp⟩

theorem Ya7Core.isMinParabolic [Finite G] (hc : Ya7Core L S α P)
    (hSH : IsSylowTwoOf S (ya7Pre L α P ⊔ S)) :
    IsMinParabolicOf (ya7Pre L α P ⊔ S) (ya7Pre L α P ⊔ S) := by
  have hlt : S < ya7Pre L α P ⊔ S := by
    refine lt_of_le_of_ne le_sup_right fun h => hc.S_not_normal ?_
    rw [← h]
    exact Subgroup.le_normalizer
  have hmax : IsMaxSubgroupIn (ya7Pre L α P ⊔ S) S := by
    refine ⟨hlt, fun K hSK hKH => ?_⟩
    rcases hc.S_maximal hSK.le hKH with h | h
    · exact absurd h (ne_of_gt hSK)
    · exact h
  have huniq : IsUniqueMaxOver (ya7Pre L α P ⊔ S) S S := by
    unfold IsUniqueMaxOver
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨⟨hmax, le_rfl⟩, fun N hN => ?_⟩
    rcases hc.S_maximal hN.2 hN.1.1.le with h | h
    · exact h
    · exact absurd h (ne_of_lt hN.1.1)
  exact (minParabolic_iff.mp ⟨hSH, hc.S_not_normal, huniq⟩).1

end CFSG.Quasithin
