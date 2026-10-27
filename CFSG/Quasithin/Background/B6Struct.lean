module

public import CFSG.Quasithin.Background.B6Basic
public import CFSG.GroupTheory.LocalCores.MinimalNormal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace B6

variable {G : Type*} [Group G]

theorem conjugate_eq_conjSub (H : Subgroup G) (g : G) : CFSG.conjugate H g = conjSub g⁻¹ H := rfl

theorem isMulCommutative_conjSub {L : Subgroup G} (hL : IsMulCommutative L) (g : G) :
    IsMulCommutative (conjSub g L) := by
  refine IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_
  rw [mem_conjSub] at ha hb
  have h := setLike_mul_comm ha hb
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
    _ = b * a := by group

theorem isSimpleGroup_conjSub {L : Subgroup G} (hL : IsSimpleGroup L) (g : G) :
    IsSimpleGroup (conjSub g L) :=
  MulEquiv.isSimpleGroup (H := L)
    (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm

theorem conjSub_le_of_normal {K L : Subgroup G} (hK : K.Normal) (hLK : L ≤ K) (g : G) :
    conjSub g L ≤ K := by
  intro x hx
  rw [mem_conjSub] at hx
  have := hK.conj_mem _ (hLK hx) g
  simpa [mul_assoc] using this

theorem le_normalizer_conjSub_of_normal {K L : Subgroup G} (hK : K.Normal)
    (hL : K ≤ Subgroup.normalizer (L : Set G)) (g : G) :
    K ≤ Subgroup.normalizer (conjSub g L : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hk' : g⁻¹ * k * g ∈ K := by simpa using hK.conj_mem k hk g⁻¹
  have e : k * g = g * (g⁻¹ * k * g) := by group
  show conjSub k (conjSub g L) = conjSub g L
  rw [← conjSub_mul, e, conjSub_mul, conjSub_eq_self (hL hk')]

theorem mul_comm_of_inf_eq_bot {K A B : Subgroup G} (hAK : A ≤ K) (hBK : B ≤ K)
    (hAn : K ≤ Subgroup.normalizer (A : Set G)) (hBn : K ≤ Subgroup.normalizer (B : Set G))
    (h : A ⊓ B = ⊥) {a b : G} (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a := by
  have h1 : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hBn (hAK ha)) b).mp hb
  have h2 : b * a⁻¹ * b⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp (hAn (hBK hb)) a⁻¹).mp (A.inv_mem ha)
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := by
    refine ⟨?_, B.mul_mem h1 (B.inv_mem hb)⟩
    have := A.mul_mem ha h2
    simpa [mul_assoc] using this
  rw [h, Subgroup.mem_bot] at h3
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

theorem le_of_inf_ne_bot_of_isSimpleGroup {K A B : Subgroup G} (hAK : A ≤ K)
    (hBn : K ≤ Subgroup.normalizer (B : Set G)) (hA : IsSimpleGroup A) (hAB : A ⊓ B ≠ ⊥) :
    A ≤ B := by
  have hnorm : ((A ⊓ B).subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro d k hd hk
    refine ⟨A.mul_mem (A.mul_mem hk hd.1) (A.inv_mem hk), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hBn (hAK hk)) d).mp hd.2
  rcases (Subgroup.isSimpleGroup_iff.mp hA).2 (A ⊓ B) inf_le_left hnorm with h | h
  · exact absurd h hAB
  · exact h.symm.le.trans inf_le_right

theorem eq_of_inf_ne_bot_of_isSimpleGroup {K A B : Subgroup G} (hAK : A ≤ K) (hBK : B ≤ K)
    (hAn : K ≤ Subgroup.normalizer (A : Set G)) (hBn : K ≤ Subgroup.normalizer (B : Set G))
    (hA : IsSimpleGroup A) (hB : IsSimpleGroup B) (hAB : A ⊓ B ≠ ⊥) : A = B :=
  le_antisymm (le_of_inf_ne_bot_of_isSimpleGroup hAK hBn hA hAB)
    (le_of_inf_ne_bot_of_isSimpleGroup hBK hAn hB (by rwa [inf_comm]))

theorem exists_eq_of_isSimpleGroup_of_normal {ι : Type*} {K N : Subgroup G} {S : ι → Subgroup G}
    (hKS : K ≤ ⨆ i, S i) (hSK : ∀ i, S i ≤ K)
    (hSn : ∀ i, K ≤ Subgroup.normalizer (S i : Set G)) (hSs : ∀ i, IsSimpleGroup (S i))
    (hNK : N ≤ K) (hNn : K ≤ Subgroup.normalizer (N : Set G)) (hNs : IsSimpleGroup N)
    (hNc : ¬ IsMulCommutative N) : ∃ i, N = S i := by
  by_contra hcon
  push Not at hcon
  have hcent : ∀ i, S i ≤ Subgroup.centralizer (N : Set G) := by
    intro i s hs
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    by_cases hbot : N ⊓ S i = ⊥
    · exact mul_comm_of_inf_eq_bot hNK (hSK i) hNn (hSn i) hbot hn hs
    · exact absurd (eq_of_inf_ne_bot_of_isSimpleGroup hNK (hSK i) hNn (hSn i) hNs (hSs i) hbot)
        (hcon i)
  have hK : K ≤ Subgroup.centralizer (N : Set G) := hKS.trans (iSup_le hcent)
  refine hNc (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_)
  exact ((Subgroup.mem_centralizer_iff.mp (hK (hNK ha))) b hb).symm

theorem coe_mulEquiv_pi_mulSingle {ι : Type*} [DecidableEq ι] {K : Subgroup G}
    {S : ι → Subgroup G} (e : ((i : ι) → S i) ≃* K)
    (he : ∀ (i : ι) (x : (j : ι) → S j), (∀ j, j ≠ i → x j = 1) → ((e x : K) : G) = x i)
    (i : ι) (s : S i) : ((e (Pi.mulSingle i s) : K) : G) = s := by
  have h1 : ∀ j, j ≠ i → (Pi.mulSingle i s : (j : ι) → S j) j = 1 :=
    fun j hj => Pi.mulSingle_eq_of_ne hj _
  simpa using he i (Pi.mulSingle i s) h1

theorem le_iSup_of_mulEquiv_pi {ι : Type*} [Finite ι] [DecidableEq ι] {K : Subgroup G}
    {S : ι → Subgroup G} (e : ((i : ι) → S i) ≃* K)
    (he : ∀ (i : ι) (x : (j : ι) → S j), (∀ j, j ≠ i → x j = 1) → ((e x : K) : G) = x i) :
    K ≤ ⨆ i, S i := by
  intro z hz
  obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
  have hmem : x ∈ (⨆ i, S i).comap (K.subtype.comp e.toMonoidHom) :=
    Subgroup.pi_mem_of_mulSingle_mem x fun i => by
      rw [Subgroup.mem_comap]
      show ((e (Pi.mulSingle i (x i)) : K) : G) ∈ ⨆ i, S i
      rw [coe_mulEquiv_pi_mulSingle e he]
      exact le_iSup S i (x i).2
  have hz' : ((e x : K) : G) ∈ ⨆ i, S i := hmem
  rwa [hx] at hz'

theorem iSupIndep_of_mulEquiv_pi {ι : Type*} [DecidableEq ι] {K : Subgroup G}
    {S : ι → Subgroup G} (e : ((i : ι) → S i) ≃* K)
    (he : ∀ (i : ι) (x : (j : ι) → S j), (∀ j, j ≠ i → x j = 1) → ((e x : K) : G) = x i) :
    iSupIndep S := by
  have hφinj : Function.Injective (K.subtype.comp e.toMonoidHom) :=
    K.subtype_injective.comp e.injective
  intro i
  rw [disjoint_iff, eq_bot_iff]
  intro z hz
  obtain ⟨hzi, hzj⟩ := Subgroup.mem_inf.mp hz
  have hle : (⨆ (j) (_ : j ≠ i), S j) ≤
      (MonoidHom.ker (Pi.evalMonoidHom (fun j => ↥(S j)) i)).map
        (K.subtype.comp e.toMonoidHom) := by
    refine iSup₂_le fun j hji s hs => ?_
    refine ⟨Pi.mulSingle j ⟨s, hs⟩, ?_, coe_mulEquiv_pi_mulSingle e he j ⟨s, hs⟩⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact Pi.mulSingle_eq_of_ne hji.symm _
  obtain ⟨y, hy, hyz⟩ := hle hzj
  have h0 : (K.subtype.comp e.toMonoidHom) (Pi.mulSingle i ⟨z, hzi⟩) = z :=
    coe_mulEquiv_pi_mulSingle e he i ⟨z, hzi⟩
  have hyy : y = Pi.mulSingle i ⟨z, hzi⟩ := hφinj (hyz.trans h0.symm)
  have hyi : y i = 1 := MonoidHom.mem_ker.mp hy
  rw [hyy, Pi.mulSingle_eq_same] at hyi
  simpa using congrArg Subtype.val hyi

theorem exists_simple_factor_of_minimal_normal {Z : Type*} [Group Z] [Finite Z] {T K : Subgroup Z}
    (hK : K.Normal) (hK1 : K ≠ ⊥) (hmin : ∀ N : Subgroup Z, N.Normal → N ≤ K → N = ⊥ ∨ N = K)
    (hTK : T ⊔ K = ⊤) (h2 : ∀ x : Z, ∃ k : ℕ, x ^ 2 ^ k ∈ K) (hns : ¬ Group.IsSolvable Z) :
    ∃ L : Subgroup Z, IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧ L ≤ K ∧
      K = ⨆ t ∈ T, conjSub t L ∧ sSupIndep {S : Subgroup Z | ∃ t ∈ T, S = conjSub t L} ∧
      ∀ t ∈ T, ((conjSub t L).subgroupOf K).Normal := by
  obtain ⟨r, S, hr, hSK, hSs, hSconj, hSnorm, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hK hK1 hmin
  obtain ⟨i₀⟩ : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hSn : ∀ i, K ≤ Subgroup.normalizer (S i : Set Z) := fun i =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hSK i)).mp (hSnorm i)
  have hKgen : K ≤ ⨆ i, S i := le_iSup_of_mulEquiv_pi e he
  have hind : iSupIndep S := iSupIndep_of_mulEquiv_pi e he
  have hL_nc : ¬ IsMulCommutative (S i₀) := by
    intro hc
    refine hns ?_
    have hSc : ∀ i, ∀ a ∈ S i, ∀ b ∈ S i, a * b = b * a := by
      intro i a ha b hb
      obtain ⟨g, hg⟩ := hSconj i₀ i
      rw [hg, conjugate_eq_conjSub] at ha hb
      exact isMulCommutative_iff_of_setLike.mp (isMulCommutative_conjSub hc g⁻¹) a ha b hb
    have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
      intro a ha b hb
      obtain ⟨x, hx⟩ := e.surjective ⟨a, ha⟩
      obtain ⟨y, hy⟩ := e.surjective ⟨b, hb⟩
      have hxy : x * y = y * x := by
        funext i
        exact Subtype.ext (hSc i _ (x i).2 _ (y i).2)
      have := congrArg (fun w => ((e w : K) : Z)) hxy
      simpa [hx, hy] using this
    have : Group.IsSolvable K :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (hKc a a.2 b b.2)
    have hp : IsPGroup 2 (Z ⧸ K) := fun q => by
      induction q using QuotientGroup.induction_on with
      | H z =>
        obtain ⟨k, hk⟩ := h2 z
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact hk
    have : Group.IsNilpotent (Z ⧸ K) := hp.isNilpotent
    exact Group.isSolvable_of_ker_le_range K.subtype (QuotientGroup.mk' K)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hmul : ∀ g : Z, ∃ k ∈ K, ∃ t ∈ T, k * t = g := by
    intro g
    have hg : g ∈ ((K ⊔ T : Subgroup Z) : Set Z) := by
      rw [sup_comm, hTK]
      exact Subgroup.mem_top g
    rw [Subgroup.normal_mul] at hg
    exact Set.mem_mul.mp hg
  have hSconjT : ∀ i, ∃ t ∈ T, S i = conjSub t (S i₀) := by
    intro i
    obtain ⟨g, hg⟩ := hSconj i₀ i
    obtain ⟨k, hk, t, ht, hkt⟩ := hmul g⁻¹
    refine ⟨t, ht, ?_⟩
    rw [hg, conjugate_eq_conjSub, ← hkt, conjSub_mul]
    exact conjSub_eq_self (le_normalizer_conjSub_of_normal hK (hSn i₀) t hk)
  have hconjS : ∀ g : Z, ∃ i, conjSub g (S i₀) = S i := fun g =>
    exists_eq_of_isSimpleGroup_of_normal hKgen hSK hSn hSs (conjSub_le_of_normal hK (hSK i₀) g)
      (le_normalizer_conjSub_of_normal hK (hSn i₀) g) (isSimpleGroup_conjSub (hSs i₀) g)
      (fun hc => hL_nc (by
        have := isMulCommutative_conjSub hc g⁻¹
        rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this))
  refine ⟨S i₀, hSs i₀, hL_nc, hSK i₀, ?_, ?_, fun t _ => ?_⟩
  · refine le_antisymm (hKgen.trans (iSup_le fun i => ?_))
      (iSup₂_le fun t _ => conjSub_le_of_normal hK (hSK i₀) t)
    obtain ⟨t, ht, hti⟩ := hSconjT i
    rw [hti]
    exact le_iSup₂ (f := fun t (_ : t ∈ T) => conjSub t (S i₀)) t ht
  · have hrange : {S' : Subgroup Z | ∃ t ∈ T, S' = conjSub t (S i₀)} = Set.range S := by
      ext S'
      constructor
      · rintro ⟨t, -, rfl⟩
        obtain ⟨j, hj⟩ := hconjS t
        exact ⟨j, hj.symm⟩
      · rintro ⟨i, rfl⟩
        exact hSconjT i
    rw [hrange]
    exact hind.sSupIndep_range
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (conjSub_le_of_normal hK (hSK i₀) t)).mpr (le_normalizer_conjSub_of_normal hK (hSn i₀) t)

end B6

theorem exists_simple_factor {Z : Type*} [Group Z] [Finite Z] {T M : Subgroup Z}
    (h : MinParabolic (⊤ : Subgroup Z) T M) (hJ : kerIn M ⊤ = ⊥) (hns : ¬ Group.IsSolvable Z) :
    ∃ L : Subgroup Z, IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
      L ≤ twoResidual (⊤ : Subgroup Z) ∧
      twoResidual (⊤ : Subgroup Z) = ⨆ t ∈ T, conjSub t L ∧
      sSupIndep {S : Subgroup Z | ∃ t ∈ T, S = conjSub t L} ∧
      ∀ t ∈ T, ((conjSub t L).subgroupOf (twoResidual (⊤ : Subgroup Z))).Normal := by
  have hKnormal : (twoResidual (⊤ : Subgroup Z)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  refine exists_simple_factor_of_minimal_normal hKnormal ?_ ?_ ?_ ?_ hns
  · exact fun hK => h.not_twoResidual_le_kerIn (hK ▸ bot_le)
  · intro N hN hNK
    rcases h.le_kerIn_or_twoResidual_le le_top
      (Subgroup.normalizer_eq_top_iff.mpr hN).ge with hle | hle
    · left
      rw [hJ] at hle
      exact le_bot_iff.mp hle
    · right
      exact le_antisymm hNK hle
  · exact sup_twoResidual_eq h.isSylow
  · exact fun x => twoResidual_isTwoQuotient (⊤ : Subgroup Z) x (Subgroup.mem_top x)

end CFSG.Quasithin
