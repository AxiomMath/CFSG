module

public import CFSG.Quasithin.Recognition.SzVBOddL24Facts
public import CFSG.Quasithin.Recognition.SzVBOddL24Perm
public import CFSG.Quasithin.EmptyFaithful.S152ZFMain
public import CFSG.Quasithin.Recognition.SzVBS5Perm

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Holt.H78 CFSG.Quasithin.F204

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem exists_mem_inf_smul_eq_of_bender {K P S V : Subgroup G}
    {n i e : ℕ} (hKP : K ≤ P) (hSyl : IsSylowTwoOf (S ⊓ K) K)
    (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hA : IsBenderAction ↥(imgK K P V) (ConjSet P V) n i e) {U U' : ConjSet P V}
    (hU : U ≠ ConjSet.base P V) (hU' : U' ≠ ConjSet.base P V) :
    ∃ k : ↥K, (k : G) ∈ S ∧ Subgroup.inclusion hKP k • U = U' := by
  obtain ⟨g, hgs, hg⟩ := exists_surjective_imgK V hKP
  have hp : IsPGroup 2 ((S ⊓ K).subgroupOf K) := hSyl.2.1.comap_subtype
  obtain ⟨Q, hQeq⟩ : ∃ Q : Sylow 2 ↥(imgK K P V),
      (Q : Subgroup ↥(imgK K P V)) = ((S ⊓ K).subgroupOf K).map g :=
    ⟨(hp.map g).toSylow fun h =>
      hSyl.2.2 (h.trans (((S ⊓ K).subgroupOf K).index_map_dvd hgs)), rfl⟩
  have hQ : (Q : Subgroup ↥(imgK K P V)) ≤
      MulAction.stabilizer ↥(imgK K P V) (ConjSet.base P V) := by
    intro q hq
    rw [hQeq] at hq
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hq
    rw [MulAction.mem_stabilizer_iff]
    show ((g t : ↥(imgK K P V)) : Equiv.Perm (ConjSet P V)) (ConjSet.base P V) =
      ConjSet.base P V
    rw [hg]
    exact Subtype.ext (OddAux.conjSub_eq_of_mem_normalizer'
      (hSV (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).1))
  obtain ⟨p, hpQ, hpU⟩ := hA.exists_mem_smul_eq hQ hU hU'
  rw [hQeq] at hpQ
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hpQ
  exact ⟨t, (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ht)).1, (hg t U).symm.trans hpU⟩

theorem mem_pCoreOf_of_toPermHom_eq_one
    (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 2 (OTwoQuot K1))
    {x : G} (hxS : x ∈ S)
    (hx : MulAction.toPermHom ↥(K1 ⊔ S) (ConjSet (K1 ⊔ S) (conjClosure Zs L2))
      ⟨x, (le_sup_right : S ≤ K1 ⊔ S) hxS⟩ = 1) : x ∈ pCoreOf 2 (K1 ⊔ S) := by
  have hS1 : S ≤ Subgroup.normalizer (K1 : Set G) := h.hyp.h1.normalizes
  have hPN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G) := sup_le Subgroup.le_normalizer hS1
  have hy : x ∈ (kerAct (K1 ⊔ S) (conjClosure Zs L2)).map (K1 ⊔ S).subtype :=
    ⟨⟨x, (le_sup_right : S ≤ K1 ⊔ S) hxS⟩, MonoidHom.mem_ker.mpr hx, rfl⟩
  refine mem_pCoreOf_sup_of_comm (L2 := K1) hS1 h.hyp.h1.pgroup h.hyp.h1.sylow hxS ?_
  intro l hl
  have hc : x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 K1 :=
    comm_mem_pCoreOf_of_mem_kerAct hRO h (n := 2) le_rfl (Or.inl hL) le_sup_left hPN hy hl
  have hlN : l⁻¹ ∈ Subgroup.normalizer ((pCoreOf 2 K1 : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K1 (K1.inv_mem hl)
  have h1 := (Subgroup.mem_normalizer_iff.mp hlN _).mp hc
  have e : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * (l⁻¹)⁻¹ = l⁻¹ * (x * l * x⁻¹) := by group
  rwa [e] at h1

theorem inf_L2_le_twistFree (hRO : RankOneListedFacts.{0})
    (h : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 2 (OTwoQuot K1)) :
    S ⊓ L2 ≤ twistFree K1 S := by
  classical
  by_contra hnot
  obtain ⟨r, hrSL, hrS0⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hS1 : S ≤ Subgroup.normalizer (K1 : Set G) := h.hyp.h1.normalizes
  have hSyl1 : IsSylowTwoOf (S ⊓ K1) K1 := h.hyp.h1.sylow
  have hS : IsPGroup 2 S := h.hyp.h1.pgroup
  have hR := F112J2.hyp111R_of_setting hRO h
  have hinf : (L2 ⊔ S) ⊓ (K1 ⊔ S) = S := F112J2.inf_L2S_K1S hR h.s3
  have hF := l24Facts_of_setting hRO h hL
  have hSpS : twistFree K1 S ≤ S := twistFree_le hS1 hS hSyl1
  set S₁ : Subgroup G := (L2 ⊔ twistFree K1 S) ⊓ (K1 ⊔ S) with hS₁def
  have hS₁S : S₁ ≤ S := (inf_le_inf_right _ (sup_le_sup_left hSpS L2)).trans hinf.le
  have hSp₁ : twistFree K1 S ≤ S₁ := le_inf le_sup_right (hSpS.trans le_sup_right)
  have hSL₁ : S ⊓ L2 ≤ S₁ :=
    le_inf (inf_le_right.trans le_sup_left) (inf_le_left.trans le_sup_right)
  have hSK₁ : S ⊓ K1 ≤ S₁ := (F204.inf_le_twistFree : S ⊓ K1 ≤ twistFree K1 S).trans hSp₁
  obtain ⟨t, htB, -, hτ1, hτ3⟩ := exists_order_three hRO h hL
  have htL2 : (t : G) ∈ Subgroup.normalizer (L2 : Set G) := h.hyp.h2.borel_le htB
  have htSK : (t : G) ∈ Subgroup.normalizer ((S ⊓ K1 : Subgroup G) : Set G) :=
    F1.borelOf_le_normalizer K1 S htB
  have htQ : (t : G) ∈ Subgroup.normalizer ((pCoreOf 2 (K1 ⊔ S) : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K1 ⊔ S) t.2
  have htSp : (t : G) ∈ Subgroup.normalizer ((twistFree K1 S : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨htSK, htQ⟩
  have htL2Sp : (t : G) ∈ Subgroup.normalizer ((L2 ⊔ twistFree K1 S : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨htL2, htSp⟩
  have htP : (t : G) ∈ Subgroup.normalizer ((K1 ⊔ S : Subgroup G) : Set G) :=
    Subgroup.le_normalizer t.2
  have htS₁ : (t : G) ∈ Subgroup.normalizer ((S₁ : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨htL2Sp, htP⟩
  set ρ := MulAction.toPermHom ↥(K1 ⊔ S) (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) with hρ
  set ω : ConjSet (K1 ⊔ S) (conjClosure Zs L2) :=
    ConjSet.base (K1 ⊔ S) (conjClosure Zs L2) with hω
  have hfix : ∀ (x : G) (hx : x ∈ K1 ⊔ S),
      x ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) → ρ ⟨x, hx⟩ ω = ω :=
    fun x hx hxV => Subtype.ext (OddAux.conjSub_eq_of_mem_normalizer' hxV)
  have hSV : S ≤ Subgroup.normalizer (conjClosure Zs L2 : Set G) := hF.S_le_normalizer
  have htV : (t : G) ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) :=
    borelOf_le_normalizer_conjClosure h htB
  have hσω : ρ t ω = ω := hfix t t.2 htV
  have hτ3' : ρ t * ρ t * ρ t = 1 := by
    rw [← pow_three']
    exact hτ3
  obtain ⟨μ, hμω, hσμ⟩ := perm_exists_fixed hF.card_five ω (ρ t) hτ1 hτ3' hσω
  have hA := isBenderAction_imgK_L24 hRO h hL
  have hrS : r ∈ S := hrSL.1
  have hrP : r ∈ K1 ⊔ S := Subgroup.mem_sup_right hrS
  have hrω : ρ ⟨r, hrP⟩ ω = ω := hfix r hrP (hSV hrS)
  have hrμ : ρ ⟨r, hrP⟩ μ ≠ ω := fun heq => hμω ((ρ ⟨r, hrP⟩).injective (heq.trans hrω.symm))
  obtain ⟨k, hkS, hk⟩ :=
    exists_mem_inf_smul_eq_of_bender (le_sup_left : K1 ≤ K1 ⊔ S) hSyl1 hSV hA hμω hrμ
  have hkK1 : (k : G) ∈ K1 := k.2
  set s₀ : G := (k : G)⁻¹ * r with hs₀
  have hs₀S : s₀ ∈ S := S.mul_mem (S.inv_mem hkS) hrS
  have hs₀S₁ : s₀ ∈ S₁ := S₁.mul_mem (S₁.inv_mem (hSK₁ ⟨hkS, hkK1⟩)) (hSL₁ hrSL)
  have hs₀P : s₀ ∈ K1 ⊔ S := Subgroup.mem_sup_right hs₀S
  have hm₀ω : ρ ⟨s₀, hs₀P⟩ ω = ω := hfix s₀ hs₀P (hSV hs₀S)
  have hm₀μ : ρ ⟨s₀, hs₀P⟩ μ = μ := by
    have e : (⟨s₀, hs₀P⟩ : ↥(K1 ⊔ S)) = (Subgroup.inclusion le_sup_left k)⁻¹ * ⟨r, hrP⟩ := rfl
    have hk' : ρ (Subgroup.inclusion le_sup_left k) μ = ρ ⟨r, hrP⟩ μ := hk
    rw [e, map_mul, map_inv, Equiv.Perm.mul_apply, ← hk', Equiv.Perm.inv_def]
    exact Equiv.symm_apply_apply _ _
  have hm₀1 : ρ ⟨s₀, hs₀P⟩ ≠ 1 := by
    intro h1
    apply hrS0
    have hq : s₀ ∈ pCoreOf 2 (K1 ⊔ S) := mem_pCoreOf_of_toPermHom_eq_one hRO h hL hs₀S h1
    have e : r = (k : G) * s₀ := by simp [hs₀]
    rw [e]
    exact Subgroup.mul_mem_sup ⟨hkS, hkK1⟩ hq
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, s₀ ^ 2 ^ k₀ = 1 := by
    obtain ⟨k₀, hk₀⟩ := hS ⟨s₀, hs₀S⟩
    exact ⟨k₀, by simpa using congrArg Subtype.val hk₀⟩
  have hm₀pow : ρ ⟨s₀, hs₀P⟩ ^ 2 ^ k₀ = 1 := by
    rw [← map_pow]
    have : (⟨s₀, hs₀P⟩ : ↥(K1 ⊔ S)) ^ 2 ^ k₀ = 1 := Subtype.ext (by simpa using hk₀)
    rw [this, map_one]
  have hts₀S₁ : (t : G) * s₀ * (t : G)⁻¹ ∈ S₁ :=
    (Subgroup.mem_normalizer_iff.mp htS₁ s₀).mp hs₀S₁
  have hyS₁ : s₀ * ((t : G) * s₀ * (t : G)⁻¹) ∈ S₁ := S₁.mul_mem hs₀S₁ hts₀S₁
  have hyS : s₀ * ((t : G) * s₀ * (t : G)⁻¹) ∈ S := hS₁S hyS₁
  have hyP : s₀ * ((t : G) * s₀ * (t : G)⁻¹) ∈ K1 ⊔ S := Subgroup.mem_sup_right hyS
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, (s₀ * ((t : G) * s₀ * (t : G)⁻¹)) ^ 2 ^ k₁ = 1 := by
    obtain ⟨k₁, hk₁⟩ := hS ⟨_, hyS⟩
    exact ⟨k₁, by simpa using congrArg Subtype.val hk₁⟩
  have hρy : ρ ⟨s₀ * ((t : G) * s₀ * (t : G)⁻¹), hyP⟩ =
      ρ ⟨s₀, hs₀P⟩ * (ρ t * ρ ⟨s₀, hs₀P⟩ * (ρ t)⁻¹) := by
    have e : (⟨s₀ * ((t : G) * s₀ * (t : G)⁻¹), hyP⟩ : ↥(K1 ⊔ S)) =
        ⟨s₀, hs₀P⟩ * (t * ⟨s₀, hs₀P⟩ * t⁻¹) := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv]
  have hypow : ρ ⟨s₀ * ((t : G) * s₀ * (t : G)⁻¹), hyP⟩ ^ 2 ^ k₁ = 1 := by
    rw [← map_pow]
    have : (⟨s₀ * ((t : G) * s₀ * (t : G)⁻¹), hyP⟩ : ↥(K1 ⊔ S)) ^ 2 ^ k₁ = 1 :=
      Subtype.ext (by simpa using hk₁)
    rw [this, map_one]
  rcases perm_s5 hF.card_five hμω (ρ ⟨s₀, hs₀P⟩) (ρ t) hm₀ω hm₀μ hσω hσμ hτ1 hτ3' hm₀1 with
    h3 | ⟨hx1, hx3⟩
  · exact hm₀1 (eq_one_of_cube_of_two_pow h3 hm₀pow)
  · rw [← hρy] at hx1 hx3
    exact hx1 (eq_one_of_cube_of_two_pow hx3 hypow)

end CFSG.Quasithin.SzVB
