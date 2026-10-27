module

public import CFSG.Quasithin.Vol2.Ch11SecOE8R
public import CFSG.Quasithin.Vol2.Ch11SecOE7L
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParL3
public import CFSG.Quasithin.Vol2.Ch11SecOE7G
public import CFSG.Quasithin.Vol2.Ch11SecOE8M
public import CFSG.Quasithin.Vol2.Ch11SecOE8N

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

namespace L3T

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Fin257.L3 CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple)
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_forall_commutator_mem_ker {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF4 : 4 ≤ Nat.card F) {X A : Subgroup G} (φ : ↥X →* SL(2, F)) (hφ : Function.Surjective φ)
    {a : G} (haA : a ∈ A) (haX : a ∈ X) (hφa : φ ⟨a, haX⟩ ≠ 1) :
    ¬ ∀ a ∈ A, ∀ x ∈ X, ⁅a, x⁆ ∈ φ.ker.map X.subtype := by
  have : IsSimpleGroup SL(2, F) := E1.RootLift.isSimpleGroup_SL2 hF4
  have hZ := SecE3.center_eq_bot_of_simple (SecE3.sl2_nonabelian (K := F))
  obtain ⟨y, hy⟩ : ∃ y : SL(2, F), φ ⟨a, haX⟩ * y ≠ y * φ ⟨a, haX⟩ := by
    by_contra h
    push Not at h
    apply hφa
    have : φ ⟨a, haX⟩ ∈ Subgroup.center SL(2, F) :=
      Subgroup.mem_center_iff.mpr fun g => (h g).symm
    rwa [hZ, Subgroup.mem_bot] at this
  obtain ⟨x, rfl⟩ := hφ y
  intro hall
  obtain ⟨k, hk, hkx⟩ := hall a haA x x.2
  have hk' : k = ⟨a, haX⟩ * x * (⟨a, haX⟩ : ↥X)⁻¹ * x⁻¹ := Subtype.ext (by
    rw [Subgroup.coe_subtype] at hkx
    rw [hkx, commutatorElement_def]
    rfl)
  have h1 : φ k = 1 := hk
  rw [hk', map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  apply hy
  calc φ ⟨a, haX⟩ * φ x = φ ⟨a, haX⟩ * φ x * (φ ⟨a, haX⟩)⁻¹ * (φ x)⁻¹ * (φ x * φ ⟨a, haX⟩) := by
        group
    _ = φ x * φ ⟨a, haX⟩ := by rw [h1, one_mul]

@[expose] noncomputable def projCoreEquiv {K : Type} [Field K] [Finite K] [CharP K 2]
    (j : Fin 2) :
    ↥(perfectCore (Q3 K j)) ≃* ↥(perfectCore ((Q3 K j).map (proj 3 K))) :=
  (MulEquiv.ofBijective ((proj 3 K).subgroupMap (perfectCore (Q3 K j)))
    ⟨fun x y h => Subtype.ext (Rk2.proj3_injOn_perfectCore j x.1 x.2 y.1 y.2
      (congrArg Subtype.val h)), (proj 3 K).subgroupMap_surjective _⟩).trans
    (MulEquiv.subgroupCongr (map_perfectCore (proj 3 K) (Q3 K j)))

omit [Finite G] in
theorem coe_projCoreEquiv {K : Type} [Field K] [Finite K] [CharP K 2] (j : Fin 2)
    (x : ↥(perfectCore (Q3 K j))) : (projCoreEquiv j x : projectiveSL 3 K) = proj 3 K x := rfl

omit [Finite G] in
theorem exists_levi_iota {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (ι : projectiveSL 3 K →* G)
    (hι : Function.Injective ι) (j : Fin 2) :
    ∃ φ : ↥((perfectCore ((Q3 K j).map (proj 3 K))).map ι) →* SL(2, K),
      Function.Surjective φ ∧ IsPGroup 2 φ.ker ∧
      ∀ (x : SL(3, K)) (hx : x ∈ perfectCore (Q3 K j))
        (hx' : ι (proj 3 K x) ∈ (perfectCore ((Q3 K j).map (proj 3 K))).map ι),
        φ ⟨ι (proj 3 K x), hx'⟩ = blk3 j ⟨x, hx⟩ := by
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set eN := projCoreEquiv (K := K) j with heN
  set eX := (perfectCore ((Q3 K j).map (proj 3 K))).equivMapOfInjective ι hι with heX
  refine ⟨(blk3 j).comp (eN.symm.toMonoidHom.comp eX.symm.toMonoidHom),
    (blk3_surjective hK4 j).comp (eN.symm.surjective.comp eX.symm.surjective), ?_, ?_⟩
  · intro x
    have hx : eN.symm (eX.symm x) ∈ (blk3 (K := K) j).ker := x.2
    obtain ⟨k, hk⟩ := blk3_ker_isPGroup ⟨n, hK⟩ j ⟨_, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (eN.symm (eX.symm x)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : eN.symm (eX.symm ((x : ↥((perfectCore ((Q3 K j).map (proj 3 K))).map ι)) ^ 2 ^ k)) =
        1 := by rw [map_pow, map_pow]; exact h1
    have h3 : (x : ↥((perfectCore ((Q3 K j).map (proj 3 K))).map ι)) ^ 2 ^ k = 1 := by
      have := congrArg (fun y => eX (eN y)) h2
      simpa using this
    exact h3
  · intro x hx hx'
    have hp : proj 3 K x ∈ perfectCore ((Q3 K j).map (proj 3 K)) := by
      rw [← map_perfectCore]
      exact ⟨x, hx, rfl⟩
    have e1 : eX.symm ⟨ι (proj 3 K x), hx'⟩ = ⟨proj 3 K x, hp⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have e2 : eN.symm ⟨proj 3 K x, hp⟩ = ⟨x, hx⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (coe_projCoreEquiv j ⟨x, hx⟩).symm
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, e1, e2]

theorem member_of_semilinear {L T A : Subgroup G} [hLn : L.Normal] (h : AlmostSimple L)
    (hT : IsSylowIn 2 T ⊤) {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* projectiveSL 3 K)
    (he : ((T ⊓ L).subgroupOf L).map e.toMonoidHom = projUnitriangular 3 K)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hcard : 2 ^ n < Nat.card A)
    (hsemi : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) → actHom e t ∈ semilinearAutGroup 3 K) :
    ∃ X : Subgroup G, X ≤ L ∧ ¬ Group.IsSolvable ↥X ∧
      E1.IsE n ⊤ T A (X ⊔ E1.tauOf ⊤ T A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4' : ∃ s : Finset K, s.card = 4 := exists_finset_card_four hK4
  set ψ := actHom e with hψdef
  have hψ : Function.Injective ψ := actHom_injective e h.centralizer_eq
  set ι : projectiveSL 3 K →* G := L.subtype.comp e.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := L.subtype_injective.comp e.symm.injective
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set E := A.map ψ with hEdef
  have h2 : ∀ α ∈ E, α * α = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hA.2 a ha, map_one]
  have hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha b hb]
  have hU : ∀ α ∈ E, ∀ u ∈ projUnitriangular 3 K, α u ∈ projUnitriangular 3 K := by
    rintro _ ⟨a, ha, rfl⟩ u hu
    exact actHom_mem_U e he (hAT ha) u hu
  have hEs : E ≤ semilinearAutGroup 3 K := by
    rintro _ ⟨a, ha, rfl⟩
    exact hsemi a (hAT ha) fun b hb => hAc a ha b hb
  have hcardE : Nat.card K < Nat.card E := by
    rw [hEdef, Subgroup.card_map_of_injective hψ, hK]
    exact hcard
  obtain ⟨u, hu, huW, hV⟩ := exists_inner_V_of_le_semilinear hn hK E h2 hc hU hEs hcardE
  have huA : ι u ∈ A := by
    obtain ⟨a, ha, hau⟩ := hu
    rw [eq_iota_of_actHom_eq e h.centralizer_eq hau] at ha
    exact ha
  have hτ : ∀ τ ∈ E1.tauOf ⊤ T A, τ ∈ T ∧ ψ τ ∈ semilinearAutGroup 3 K := by
    intro τ hτm
    have hτT := E1.tauOf_le _ _ _ hτm
    refine ⟨hτT, hsemi τ hτT fun a ha => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (tauOf_le_centralizer h ha hτm)
  have hTL : (projUnitriangular 3 K).map ι = T ⊓ L := by
    rw [← he, Subgroup.map_map]
    have hcomp : ι.comp e.toMonoidHom = L.subtype := by
      ext x
      simp [hιdef]
    rw [hcomp, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  have hTLs : IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal (⟨hT.1, hT.2.1, hT.2.2⟩ : IsSylowTwoOf T ⊤) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have pkg₀ := Rk2.rank2Pkg_proj3 hK hn
  have key : ∀ (j : Fin 2) (x₀ : SL(3, K)) (hx₀ : x₀ ∈ perfectCore (Q3 K j)),
      ι (proj 3 K x₀) ∈ A → blk3 j ⟨x₀, hx₀⟩ ≠ 1 →
        ∃ X : Subgroup G, X ≤ L ∧ ¬ Group.IsSolvable ↥X ∧
          E1.IsE n ⊤ T A (X ⊔ E1.tauOf ⊤ T A) := by
    intro j x₀ hx₀ hA₀ hb
    set X := (perfectCore ((Q3 K j).map (proj 3 K))).map ι with hX
    obtain ⟨φ, hφs, hφk, hφv⟩ := exists_levi_iota hK hn ι hι j
    have hx₀X : ι (proj 3 K x₀) ∈ X :=
      ⟨proj 3 K x₀, by rw [← map_perfectCore]; exact ⟨x₀, hx₀, rfl⟩, rfl⟩
    have hXL : X ≤ L := by
      rintro _ ⟨p, -, rfl⟩
      exact (e.symm p).2
    have hXs : ¬ Group.IsSolvable ↥X := fun hs =>
      SzN2.not_isSolvable_sl2 hK4' (Group.isSolvable_of_surjective hφs)
    have hτN : E1.tauOf ⊤ T A ≤ Subgroup.normalizer (X : Set G) := by
      intro τ hτm
      obtain ⟨hτT, hτs⟩ := hτ τ hτm
      apply mem_normalizer_map_iota e
      rw [map_perfectCore, map_Q3_of_mem_semilinear hτs (actHom_mem_U e he hτT) j]
    have hL : IsSylowIn 2 (T ⊓ X) X := by
      set Pj := ((Q3 K j).map (proj 3 K)).map ι with hPj
      have hUP : T ⊓ L ≤ Pj := by
        rw [← hTL]
        exact Subgroup.map_mono (pkg₀.res.2.1 j)
      have hPL : Pj ≤ L := by
        rintro _ ⟨p, -, rfl⟩
        exact (e.symm p).2
      have h1 := B6.isSylowTwoOf_mono hTLs hUP hPL
      have hXP : X ≤ Pj := Subgroup.map_mono (perfectCore_le _)
      have hPN : Pj ≤ Subgroup.normalizer (X : Set G) := by
        rintro _ ⟨p, hp, rfl⟩
        have hpn : p ∈ Subgroup.normalizer
            ((perfectCore ((Q3 K j).map (proj 3 K)) : Subgroup (projectiveSL 3 K)) :
              Set (projectiveSL 3 K)) :=
          normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer hp)
        apply mem_normalizer_map_iota e
        rw [show ι p = ((e.symm p : ↥L) : G) from rfl, actHom_of_mem e (e.symm p).2]
        simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]
        exact A1b.conjSub_eq_iff_mem_normalizer.mpr hpn
      have h2 := B6.isSylowTwoOf_inf_normal h1 hXP hPN
      rw [inf_assoc, inf_eq_right.mpr hXL] at h2
      exact ⟨h2.1, h2.2.1, h2.2.2⟩
    have hAC := not_forall_commutator_mem_ker hK4 φ hφs hA₀ hx₀X
      (by rw [hφv x₀ hx₀ hx₀X]; exact hb)
    exact ⟨X, hXL, hXs, isE_sup_tauOf_of_quot_sl2 hT hAT hA φ hφs hφk hK hK4 hτN hL hAC⟩
  rcases hV with hV1 | hV2
  · obtain ⟨a₀, c, rfl⟩ := mem_V1.mp hV1
    have ha₀ : a₀ ≠ 0 := fun h0 => huW ⟨c, by rw [h0, xP_zero, one_mul]⟩
    refine key 1 (xMat a₀ * wMat c) (xMat_mul_wMat_mem hK4' a₀ c) (by rw [map_mul]; exact huA)
      fun h1 => ha₀ ?_
    have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h1
    simp only [blk3_xMat_mul_wMat] at this
    simpa using this
  · obtain ⟨b₀, c, rfl⟩ := mem_V2.mp hV2
    have hb₀ : b₀ ≠ 0 := fun h0 => huW ⟨c, by rw [h0, yP_zero, one_mul]⟩
    refine key 0 (yMat b₀ * wMat c) (yMat_mul_wMat_mem hK4' b₀ c) (by rw [map_mul]; exact huA)
      fun h1 => hb₀ ?_
    have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h1
    simp only [blk3_yMat_mul_wMat] at this
    simpa using this

end L3T

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
