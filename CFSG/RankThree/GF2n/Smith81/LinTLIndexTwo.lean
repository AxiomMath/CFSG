module

public import CFSG.RankThree.GF2n.Smith81.Sec117
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z A : Subgroup G}

theorem Ctx.mem_sup_of_comm_index_two (hc : Ctx M Q Z A) {R : Subgroup G}
    (hR : R ≤ Q ⊓ Subgroup.centralizer (A : Set G))
    (hRi : (R.subgroupOf (Q ⊓ Subgroup.centralizer (A : Set G))).index ≤ 2)
    {x : G} (hx : x ∈ Q) (hxc : ∀ y ∈ R, x * y = y * x) : x ∈ A ⊔ Z := by
  classical
  obtain ⟨K, hK, hfin, -, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨b, hb0, -, hAb, hcent, -⟩ := hc.dictB h
  have hK4 : 4 ≤ Nat.card K := by
    rw [h.card]
    exact hc.hyp.q4
  have hcoset : ∀ y ∈ Q ⊓ Subgroup.centralizer (A : Set G), ∀ r ∈ R,
      M₀.B (M₀.π x) (M₀.π (y * r)) = M₀.B (M₀.π x) (M₀.π y) := by
    intro y hy r hr
    have hrQ : r ∈ Q := (Subgroup.mem_inf.mp (hR hr)).1
    have hyQ : y ∈ Q := (Subgroup.mem_inf.mp hy).1
    have hrB : M₀.B (M₀.π x) (M₀.π r) = 0 :=
      (M₀.comm_iff_B h.reg hx hrQ).mp (hxc r hr)
    rw [M₀.π_mul y hyQ r hrQ, map_add, hrB, add_zero]
  have key : ∀ v : M₀.E, M₀.B v b = 0 → M₀.B (M₀.π x) v = 0 := by
    intro v hv
    by_contra hne
    have hex : ∀ k : K, ∃ y : G, y ∈ Q ⊓ Subgroup.centralizer (A : Set G) ∧
        M₀.π y = k • v := by
      intro k
      obtain ⟨y, hyQ, hy⟩ := M₀.π_surj (k • v)
      refine ⟨y, Subgroup.mem_inf.mpr ⟨hyQ, (hcent y hyQ).mpr ?_⟩, hy⟩
      rw [hy, map_smul, LinearMap.smul_apply, hv, smul_zero]
    choose yk hyk using hex
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fintype (↥(Q ⊓ Subgroup.centralizer (A : Set G)) ⧸
        R.subgroupOf (Q ⊓ Subgroup.centralizer (A : Set G))) := Fintype.ofFinite _
    have hcard : Fintype.card (↥(Q ⊓ Subgroup.centralizer (A : Set G)) ⧸
        R.subgroupOf (Q ⊓ Subgroup.centralizer (A : Set G))) < Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      have hidx : Nat.card (↥(Q ⊓ Subgroup.centralizer (A : Set G)) ⧸
          R.subgroupOf (Q ⊓ Subgroup.centralizer (A : Set G))) =
          (R.subgroupOf (Q ⊓ Subgroup.centralizer (A : Set G))).index := rfl
      omega
    obtain ⟨k, k', hkk, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : K => (QuotientGroup.mk ⟨yk k, (hyk k).1⟩ :
        ↥(Q ⊓ Subgroup.centralizer (A : Set G)) ⧸
          R.subgroupOf (Q ⊓ Subgroup.centralizer (A : Set G)))) hcard
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hg
    have hr : (yk k)⁻¹ * yk k' ∈ R := by simpa using hg
    have e := hcoset (yk k) (hyk k).1 ((yk k)⁻¹ * yk k') hr
    rw [mul_inv_cancel_left, (hyk k').2, (hyk k).2, map_smul, map_smul, smul_eq_mul,
      smul_eq_mul] at e
    exact hkk (mul_right_cancel₀ hne e).symm
  obtain ⟨c, hc'⟩ := Tim79.QuadModel.exists_smul_of_orthogonal hb0 key
  have hmem : M₀.π x ∈ M₀.img (A ⊔ Z) := M₀.img_mono le_sup_left ((hAb _).mpr ⟨c, hc'⟩)
  exact (M₀.mem_img_iff le_sup_right hx).mp hmem

theorem Ctx.mem_sup_of_comm_QB_inf_M_index_two (hc : Ctx M Q Z A) {R : Subgroup G}
    (hR : R ≤ QB A ⊓ M) (hRi : (R.subgroupOf (QB A ⊓ M)).index ≤ 2)
    {y : G} (hy : y ∈ QB A) (hyc : ∀ l ∈ R, y * l = l * y) : y ∈ A ⊔ Z := by
  obtain ⟨n, h1, -, h3, h4⟩ := hc.exists_swap'
  have hyQ : n⁻¹ * y * n ∈ Q := by
    rw [← h1, mem_conjSubgroup] at hy
    exact hy
  have hN : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    apply le_normalizer_of_comm
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp ha b hb).symm
  have hTm : ∀ c ∈ Q ⊓ Subgroup.centralizer (A : Set G), n * c * n⁻¹ ∈ QB A ⊓ M := by
    intro c hc'
    obtain ⟨hcQ, hcC⟩ := Subgroup.mem_inf.mp hc'
    have e : n⁻¹ * (n * c * n⁻¹) * n = c := by group
    have hlQB : n * c * n⁻¹ ∈ QB A := by
      rw [← h1, mem_conjSubgroup, e]
      exact hcQ
    have hlM : n * c * n⁻¹ ∈ M := by
      rw [← hc.hyp.normalizer_Z.1, ← h4, mem_normalizer_conj_iff, e]
      exact hN hcC
    exact Subgroup.mem_inf.mpr ⟨hlQB, hlM⟩
  let f : G →* G := (MulAut.conj n).toMonoidHom
  have hf : ∀ c : G, f c = n * c * n⁻¹ := fun c => rfl
  have hmap : Subgroup.map f (Q ⊓ Subgroup.centralizer (A : Set G)) ≤ QB A ⊓ M := by
    rintro _ ⟨c, hc', rfl⟩
    rw [hf]
    exact hTm c hc'
  have hne : R.relIndex (QB A ⊓ M) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hRi' : (Subgroup.comap f R ⊓ (Q ⊓ Subgroup.centralizer (A : Set G))).relIndex
      (Q ⊓ Subgroup.centralizer (A : Set G)) ≤ 2 := by
    rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]
    exact le_trans (Subgroup.relIndex_le_of_le_right hmap hne) hRi
  have hxc : ∀ c ∈ Subgroup.comap f R ⊓ (Q ⊓ Subgroup.centralizer (A : Set G)),
      n⁻¹ * y * n * c = c * (n⁻¹ * y * n) := by
    intro c hc'
    have hcR : n * c * n⁻¹ ∈ R := by
      have hc'' := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hc').1
      rwa [hf] at hc''
    have hyl := hyc (n * c * n⁻¹) hcR
    have e1 : n⁻¹ * y * n * c = n⁻¹ * (y * (n * c * n⁻¹)) * n := by group
    have e2 : c * (n⁻¹ * y * n) = n⁻¹ * ((n * c * n⁻¹) * y) * n := by group
    rw [e1, e2, hyl]
  have hmem : n⁻¹ * y * n ∈ A ⊔ Z :=
    Ctx.mem_sup_of_comm_index_two hc inf_le_right hRi' hyQ hxc
  have hmem' : y ∈ conjSubgroup n (A ⊔ Z) := mem_conjSubgroup.mpr hmem
  rw [conjSubgroup_sup', h4, h3, sup_comm] at hmem'
  exact hmem'

theorem Ctx.inf_QB_inf_eq_of_sup_inf_sub (hc : Ctx M Q Z A) {V P : Subgroup G} (hZV : Z ≤ V)
    (hPL : P ≤ LB M Q A) (hPn : P ≤ Subgroup.normalizer (V : Set G))
    (hPi : ((QB A ⊓ M ⊓ P).subgroupOf (QB A ⊓ M)).index ≤ 2)
    (hAV : (A ⊔ Z) ⊓ V = Z) : Q ⊓ QB A ⊓ V = Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, S = Q ⊓ QB A ⊓ V := ⟨_, rfl⟩
  rw [← hS]
  have hmemS : ∀ g : G, g ∈ S ↔ g ∈ Q ∧ g ∈ QB A ∧ g ∈ V := by
    intro g
    simp only [hS, Subgroup.mem_inf, and_assoc]
  have hSQ : S ≤ Q := fun g hg => ((hmemS g).mp hg).1
  have hSD : S ≤ QB A := fun g hg => ((hmemS g).mp hg).2.1
  have hSV : S ≤ V := fun g hg => ((hmemS g).mp hg).2.2
  have hZS : Z ≤ S := fun z hz => (hmemS z).mpr ⟨hc.Z_le_Q hz, hc.Z_le_QB.1 hz, hZV hz⟩
  refine le_antisymm ?_ hZS
  by_contra hSZ
  have hconjQ : ∀ x ∈ Q, ∀ h ∈ Q ⊓ QB A, x * h * x⁻¹ ∈ Q ⊓ QB A := by
    intro x hx h hh
    obtain ⟨hhQ, hhD⟩ := Subgroup.mem_inf.mp hh
    refine Subgroup.mem_inf.mpr ⟨Q.mul_mem (Q.mul_mem hx hhQ) (Q.inv_mem hx), ?_⟩
    have hcomm : ⁅x, h⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx hhQ
    have e : x * h * x⁻¹ = ⁅x, h⁆ * h := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (QB A).mul_mem (hc.Z_le_QB.1 hcomm) hhD
  have hconjM : ∀ s ∈ QB A ⊓ M, ∀ h ∈ Q ⊓ QB A, s * h * s⁻¹ ∈ Q ⊓ QB A := by
    intro s hs h hh
    obtain ⟨hhQ, hhD⟩ := Subgroup.mem_inf.mp hh
    have hsD : s ∈ QB A := (Subgroup.mem_inf.mp hs).1
    have hsM : s ∈ M := (Subgroup.mem_inf.mp hs).2
    refine Subgroup.mem_inf.mpr ⟨?_, (QB A).mul_mem ((QB A).mul_mem hsD hhD) ((QB A).inv_mem hsD)⟩
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) h).mp hhQ
  have hnT : Q ⊔ (QB A ⊓ M) ≤ Subgroup.normalizer ((Q ⊓ QB A : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => hconjQ x hx h hh, fun hh => ?_⟩
      have h' := hconjQ x⁻¹ (Q.inv_mem hx) _ hh
      have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rwa [e] at h'
    · intro s hs
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => hconjM s hs h hh, fun hh => ?_⟩
      have h' := hconjM s⁻¹ ((QB A ⊓ M).inv_mem hs) _ hh
      have e : s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h := by group
      rwa [e] at h'
  have hnP : P ≤ Subgroup.normalizer ((Q ⊓ QB A : Subgroup G) : Set G) :=
    fun l hl => hnT (hPL hl)
  have hnS : P ≤ Subgroup.normalizer (S : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hT := Subgroup.mem_normalizer_iff.mp (hnP hl) h
    have hV := Subgroup.mem_normalizer_iff.mp (hPn hl) h
    simp only [SetLike.mem_coe, Subgroup.mem_inf] at hT hV
    simp only [SetLike.mem_coe, hmemS]
    tauto
  have hP2 : IsPGroup 2 P := by
    intro l
    obtain ⟨k, hk⟩ := CFSG.RankThree.GF2n.Smith81.Sec117.isPGroup_LB hc ⟨l.1, hPL l.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hS2 : IsPGroup 2 S := (CFSG.RankThree.GF2n.Smith81.isPGroup_Q' hc.hyp).to_le hSQ
  let f : ↥P → ↥S → ↥S := fun l x =>
    ⟨(l : G) * x * (l : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hnS l.2) x).mp x.2⟩
  have hf : ∀ (l : ↥P) (a b : ↥S), a⁻¹ * b ∈ Z.subgroupOf S →
      (f l a)⁻¹ * f l b ∈ Z.subgroupOf S := by
    intro l a b hab
    rw [Subgroup.mem_subgroupOf] at hab ⊢
    have hab' : (a : G)⁻¹ * (b : G) ∈ Z := by simpa using hab
    have e : (((f l a)⁻¹ * f l b : ↥S) : G) = (l : G) * ((a : G)⁻¹ * (b : G)) * (l : G)⁻¹ := by
      simp only [f, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, hc.LB_centralizes_Z (hPL l.2) _ hab']
    exact hab'
  letI act : MulAction ↥P (↥S ⧸ Z.subgroupOf S) :=
    { smul := fun l => Quotient.map' (f l) (fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab ⊢
        exact hf l a b hab)
      one_smul := fun q => by
        induction q using QuotientGroup.induction_on with
        | H x => exact congrArg _ (Subtype.ext (by simp [f]))
      mul_smul := fun l₁ l₂ q => by
        induction q using QuotientGroup.induction_on with
        | H x => exact congrArg _ (Subtype.ext (by simp only [f, Subgroup.coe_mul]; group)) }
  have hsmul : ∀ (l : ↥P) (x : ↥S),
      (l • (x : ↥S ⧸ Z.subgroupOf S)) = ((f l x : ↥S) : ↥S ⧸ Z.subgroupOf S) :=
    fun l x => rfl
  have hidx : 2 ∣ Nat.card (↥S ⧸ Z.subgroupOf S) := by
    rw [← Subgroup.index]
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    have hdvd : (Z.subgroupOf S).index ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases j with _ | j
    · exfalso
      rw [pow_zero, Subgroup.index_eq_one] at hj
      apply hSZ
      intro g hg
      have hmem : (⟨g, hg⟩ : ↥S) ∈ Z.subgroupOf S := by
        rw [hj]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    · rw [hj, pow_succ]
      exact dvd_mul_left _ _
  have hmod := hP2.card_modEq_card_fixedPoints (↥S ⧸ Z.subgroupOf S)
  have hfix2 : 2 ∣ Nat.card (MulAction.fixedPoints ↥P (↥S ⧸ Z.subgroupOf S)) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hidx))
  have h1fix : ((1 : ↥S) : ↥S ⧸ Z.subgroupOf S) ∈
      MulAction.fixedPoints ↥P (↥S ⧸ Z.subgroupOf S) := by
    intro l
    rw [hsmul]
    exact congrArg _ (Subtype.ext (by simp [f]))
  obtain ⟨q, hqfix, hq1⟩ : ∃ q ∈ MulAction.fixedPoints ↥P (↥S ⧸ Z.subgroupOf S),
      q ≠ ((1 : ↥S) : ↥S ⧸ Z.subgroupOf S) := by
    by_contra hcon
    push Not at hcon
    have hsub : (MulAction.fixedPoints ↥P (↥S ⧸ Z.subgroupOf S)).Subsingleton :=
      fun a ha b hb => (hcon a ha).trans (hcon b hb).symm
    have hcard : Nat.card (MulAction.fixedPoints ↥P (↥S ⧸ Z.subgroupOf S)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨hsub.coe_sort, ⟨⟨_, h1fix⟩⟩⟩
    omega
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hyZ : (y : G) ∉ Z := fun h => hq1 (by
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using h)
  have hyQ : (y : G) ∈ Q := hSQ y.2
  have hcomm : ∀ l ∈ P, ⁅(y : G), l⁆ ∈ Z := by
    intro l hl
    have h := hqfix ⟨l, hl⟩
    rw [hsmul, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    have hw : (((f ⟨l, hl⟩ y)⁻¹ * y : ↥S) : G) = (l * (y : G) * l⁻¹)⁻¹ * (y : G) := rfl
    rw [hw] at h
    have e : ⁅(y : G), l⁆ = (y : G) * ((l * (y : G) * l⁻¹)⁻¹ * (y : G)) * (y : G)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hc.conj_Z_of_mem_Q hyQ h]
    exact h
  have hcommR : ∀ l ∈ QB A ⊓ M ⊓ P, (y : G) * l = l * (y : G) := by
    intro l hl
    obtain ⟨hlDM, hlP⟩ := Subgroup.mem_inf.mp hl
    have hlD : l ∈ QB A := (Subgroup.mem_inf.mp hlDM).1
    have hz : ⁅(y : G), l⁆ ∈ Z ⊓ A :=
      Subgroup.mem_inf.mpr ⟨hcomm l hlP, hc.comm_QB_le_B (hSD y.2) hlD⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hz
    exact hz
  have hyA : (y : G) ∈ A ⊔ Z :=
    Ctx.mem_sup_of_comm_QB_inf_M_index_two hc inf_le_left hPi (hSD y.2) hcommR
  have hyBZ : (y : G) ∈ (A ⊔ Z) ⊓ V := Subgroup.mem_inf.mpr ⟨hyA, hSV y.2⟩
  rw [hAV] at hyBZ
  exact hyZ hyBZ

end CFSG.RankThree.GF2n.Stroth80
