module

public import CFSG.Quasithin.MS93.ASSL3
public import CFSG.Quasithin.MS93.ASHyp
public import CFSG.Quasithin.MS93.ASBlocks

public section

namespace CFSG.Quasithin.MS93

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped Pointwise

theorem card_statedSL3_two : Nat.card ↥(StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

theorem ncard_ne_zero_vec : {v : Fin 3 → ZMod 2 | v ≠ 0}.ncard = 7 := by
  rw [Set.ncard_eq_toFinset_card']
  rfl

theorem statedSL3_smul_def (γ : ↥(StatedSL 3 (ZMod 2))) (v : Fin 3 → ZMod 2) :
    γ • v = ((γ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec v := rfl

theorem statedSL3_smul_zero (γ : ↥(StatedSL 3 (ZMod 2))) : γ • (0 : Fin 3 → ZMod 2) = 0 :=
  (statedSL3_smul_def γ 0).trans (Matrix.mulVec_zero _)

theorem index_stabilizer_statedSL3_two {w : Fin 3 → ZMod 2} (hw : w ≠ 0) :
    (MulAction.stabilizer ↥(StatedSL 3 (ZMod 2)) w).index = 7 := by
  rw [MulAction.index_stabilizer]
  have horb : MulAction.orbit ↥(StatedSL 3 (ZMod 2)) w = {v | v ≠ 0} := by
    ext v
    constructor
    · rintro ⟨γ, rfl⟩ h0
      change γ • w = 0 at h0
      apply hw
      rw [← inv_smul_smul γ w, h0, statedSL3_smul_zero]
    · intro hv
      obtain ⟨γ, hγ⟩ := statedSL3_transitive w v hw hv
      exact ⟨γ, hγ⟩
  rw [horb, ncard_ne_zero_vec]

variable {G : Type} [Group G] [Finite G]

theorem ker_eq_of_case8 {G₀ R L : Subgroup G} (hMS : IsMSPair G₀ R) (hL : L ∈ cComp G₀)
    (hG : (G₀ : Set G) = (L : Set G) * (R : Set G)) (h : PUHyp G₀ R L)
    {α : ↥G₀ →* ↥(StatedSL 3 (ZMod 2))} (hα : Function.Surjective α)
    (hn : IsSumOfNaturalModulesVia G₀ (Vq G₀ L)
      (Vq G₀ L ⊓ Subgroup.centralizer (G₀ : Set G)) α false 1) :
    α.ker = CFSG.pCore 2 ↥G₀ := by
  refine le_antisymm (ker_le_pCore_of_odd α fun g hg hodd => ?_)
    (pCore_le_ker_of_surjective α hα (statedSL3_normal_isPGroup_eq_bot (ZMod 2)))
  have hodd' : Odd (orderOf (g : G)) := by rwa [Subgroup.orderOf_coe]
  have hgL : (g : G) ∈ L := by
    rw [isMSPair_eq_oddGen hMS hL hG]
    exact Subgroup.subset_closure ⟨g.2, hodd'⟩
  have hA : Vq G₀ L ⊓ Subgroup.centralizer (G₀ : Set G) ≤ pCoreOf 2 G₀ :=
    inf_le_left.trans (Vq_le_pCoreOf h.L_le)
  have hV := commute_step hodd' hA
    (fun a ha => Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 g g.2)
    (fun b hb => commutator_mem_of_mem_ker hn hg hb)
  exact Subtype.ext (eq_one_of_odd_of_commute h.charTwo h.L_le hgL hodd' hV)

theorem surjective_comp_of_case8 {G₀ R L : Subgroup G} (h : PUHyp G₀ R L)
    {α : ↥G₀ →* ↥(StatedSL 3 (ZMod 2))} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥G₀) :
    Function.Surjective (α.comp (Subgroup.inclusion h.L_le)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α' := α.comp (Subgroup.inclusion h.L_le) with hα'
  have hq : CFSG.IsQuasisimple ↥(StatedSL 3 (ZMod 2)) :=
    EmptyFaithfulMultiple.FFL.isQuasisimple_statedSL (m := 2) le_rfl (ZMod 2)
  have hq' : CFSG.Open.IsQuasisimple ↥(StatedSL 3 (ZMod 2)) :=
    ⟨Group.isPerfect_def.1 hq.1, hq.2.1⟩
  have hLn : (L.subgroupOf G₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hrange : α'.range = (L.subgroupOf G₀).map α := by
    rw [hα', MonoidHom.range_comp]
    congr 1
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hN : α'.range.Normal := hrange ▸ Subgroup.Normal.map hLn α hα
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq' α'.range
    with hc | ht
  · exfalso
    rw [center_statedSL3_two_eq_bot, le_bot_iff, MonoidHom.range_eq_bot_iff] at hc
    have hLQ : L ≤ pCoreOf 2 G₀ := fun x hx => by
      have h1 : α' ⟨x, hx⟩ = 1 := by rw [hc]; rfl
      have h2 : (⟨x, h.L_le hx⟩ : ↥G₀) ∈ α.ker := h1
      rw [hker, ← pCoreOf_subgroupOf] at h2
      exact Subgroup.mem_subgroupOf.mp h2
    exact h.L_ne_bot (eq_bot_of_perfect_of_isPGroup h.perfect
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₀).to_le hLQ))
  · exact MonoidHom.range_eq_top.mp ht

theorem isC134Case5_of_case8 {G₀ R L : Subgroup G} (hMS : IsMSPair G₀ R) (hL : L ∈ cComp G₀)
    (hG : (G₀ : Set G) = (L : Set G) * (R : Set G)) (h : PUHyp G₀ R L)
    (h8 : MS93Case8 G₀ R L) : IsC134Case5 G₀ R L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨α, hα, hn⟩, hcard, hTQ, hcomm, hCML, hVU, hX, hSyl⟩ := id h8
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨α', hmod, hn'⟩ := isModO2Surj_of_case8 h h8
    refine ⟨α', hmod, ?_, ?_⟩
    · show Nat.card ↥(Vq G₀ L ⊓ Subgroup.centralizer (L : Set G)) = 2
      rw [← hCML]
      exact hcard
    · show IsSumOfNaturalModulesVia L (Vq G₀ L) (Vq G₀ L ⊓ Subgroup.centralizer (L : Set G))
        α' false 1
      rw [← hCML]
      exact hn'
  set CV := Vq G₀ L ⊓ Subgroup.centralizer (G₀ : Set G) with hCV
  have hCQ : c134CQ G₀ L = CV := hCML.symm
  have hker := ker_eq_of_case8 hMS hL hG h hα hn
  have hQ' : α.ker = (pCoreOf 2 G₀).subgroupOf G₀ := hker.trans (pCoreOf_subgroupOf G₀).symm
  obtain ⟨hMV, -, β, -, hβk, hβeq⟩ := hn
  set vec : ↥(Vq G₀ L) → Fin 3 → ZMod 2 := fun u => Multiplicative.toAdd (β u) 0 with hvec
  have hvec_mul : ∀ u u' : ↥(Vq G₀ L), vec (u * u') = vec u + vec u' := fun u u' => by
    simp only [hvec, map_mul, toAdd_mul, Pi.add_apply]
  have hvec0 : ∀ u : ↥(Vq G₀ L), vec u = 0 ↔ (u : G) ∈ CV := fun u => by
    rw [← Subgroup.mem_subgroupOf, ← hβk, MonoidHom.mem_ker]
    constructor
    · intro h0
      apply Multiplicative.toAdd.injective
      funext i
      rw [Subsingleton.elim i 0]
      exact h0
    · intro h1
      simp only [hvec, h1, toAdd_one, Pi.zero_apply]
  have hvec_inv : ∀ u : ↥(Vq G₀ L), vec u⁻¹ = -vec u := fun u => by
    have h1 : vec (u⁻¹ * u) = 0 := (hvec0 _).mpr (by
      rw [inv_mul_cancel, OneMemClass.coe_one]
      exact CV.one_mem)
    rw [hvec_mul] at h1
    exact eq_neg_of_add_eq_zero_left h1
  have hvec_conj : ∀ (g : ↥G₀) (u v : ↥(Vq G₀ L)), (v : G) = g * u * g⁻¹ →
      vec v = α g • vec u := fun g u v huv => by
    have := hβeq g u v huv 0
    simp only [moduleAct, Bool.false_eq_true, ↓reduceIte] at this
    exact this
  set X := ⁅Vq G₀ L, R⁆ ⊔ CV with hXdef
  have hXV : X ≤ Vq G₀ L :=
    sup_le (commutator_le_left_of_le_normalizer (h.le.trans hMV)) inf_le_left
  have hH2 : (CV.subgroupOf X).index = 2 := hcomm
  obtain ⟨a, ha⟩ : ∃ a : ↥X, a ∉ CV.subgroupOf X := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have htop : CV.subgroupOf X = ⊤ := eq_top_iff.mpr fun b _ => hcon b
    rw [htop, Subgroup.index_top] at hH2
    exact absurd hH2 (by norm_num)
  have hdich : ∀ b : ↥X, b ∈ CV.subgroupOf X ∨ b * a ∈ CV.subgroupOf X := fun b => by
    by_cases hb : b ∈ CV.subgroupOf X
    · exact Or.inl hb
    · exact Or.inr ((Subgroup.mul_mem_iff_of_index_two hH2).mpr (iff_of_false hb ha))
  set q : G := (a : G) with hq
  have hqX : q ∈ X := a.2
  have hqV : q ∈ Vq G₀ L := hXV hqX
  have hqCV : q ∉ CV := fun hc => ha (Subgroup.mem_subgroupOf.mpr hc)
  set w := vec ⟨q, hqV⟩ with hw
  have hw0 : w ≠ 0 := fun h0 => hqCV ((hvec0 _).mp h0)
  set G₁' : Subgroup ↥G₀ := (MulAction.stabilizer ↥(StatedSL 3 (ZMod 2)) w).comap α with hG₁'
  set G₁ : Subgroup G := G₁'.map G₀.subtype with hG₁
  have hkey : ∀ g : ↥G₀, g ∈ G₁' ↔ (g : G) * q * (g : G)⁻¹ * q⁻¹ ∈ CV := fun g => by
    have hv : (g : G) * q * (g : G)⁻¹ ∈ Vq G₀ L :=
      (Subgroup.mem_normalizer_iff.mp (hMV g.2) q).mp hqV
    have e1 : vec ⟨_, hv⟩ = α g • w := hvec_conj g ⟨q, hqV⟩ ⟨_, hv⟩ rfl
    have e2 : (g : G) * q * (g : G)⁻¹ * q⁻¹ =
        ((⟨_, hv⟩ * (⟨q, hqV⟩ : ↥(Vq G₀ L))⁻¹ : ↥(Vq G₀ L)) : G) := rfl
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, e2, ← hvec0, hvec_mul, hvec_inv, e1]
    constructor
    · intro hw'
      rw [hw']
      exact add_neg_cancel w
    · intro h0
      exact add_neg_eq_zero.mp h0
  have hmemG₁ : ∀ g : G, g ∈ G₁ ↔ g ∈ G₀ ∧ g * q * g⁻¹ * q⁻¹ ∈ c134CQ G₀ L := fun g => by
    rw [hCQ]
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, (hkey g').mp hg'⟩
    · rintro ⟨hg, hc⟩
      exact ⟨⟨g, hg⟩, (hkey ⟨g, hg⟩).mpr hc, rfl⟩
  have hG₁sub : G₁.subgroupOf G₀ = G₁' := by
    rw [hG₁, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective G₀.subtype_injective]
  have hG₁idx : G₁'.index = 7 := by
    rw [hG₁', Subgroup.index_comap_of_surjective _ hα, index_stabilizer_statedSL3_two hw0]
  have hG₁rel : G₁.relIndex G₀ = 7 := by
    show (G₁.subgroupOf G₀).index = 7
    rw [hG₁sub, hG₁idx]
  have hQidx : α.ker.index = 168 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hα, Subgroup.card_top,
      card_statedSL3_two]
  have hQG₁ : α.ker ≤ G₁' := fun k hk => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hk]
    exact Subgroup.one_mem _
  have hQG₁idx : α.ker.relIndex G₁' = 24 := by
    have e := Subgroup.relIndex_mul_index hQG₁
    rw [hQidx, hG₁idx] at e
    omega
  have hodd : IsOddRadical G₀ R := by
    rcases hMS.2.1 with ha' | hb
    · exact isOddRadical_of_msPair h.le ha'
    · exfalso
      have h1 : (CFSG.pCore 2 ↥G₀).index = 12096 := hb.2.2.1.1
      rw [← hker, hQidx] at h1
      exact absurd h1 (by norm_num)
  set N' : Subgroup ↥G₀ := (Subgroup.normalizer (R : Set G)).subgroupOf G₀ with hN'
  have hXN : G₀ ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    have h1 : G₀ ⊓ Subgroup.normalizer (R : Set G) ≤
        Subgroup.normalizer ((⁅Vq G₀ L, R⁆ : Subgroup G) : Set G) :=
      le_normalizer_commutator (inf_le_left.trans hMV) inf_le_right
    have h2 : G₀ ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (CV : Set G) :=
      inf_le_left.trans (le_normalizer_inf hMV (le_normalizer_centralizer Subgroup.le_normalizer))
    exact fun n hn => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨h1 hn, h2 hn⟩
  have hNG₁ : N' ≤ G₁' := fun n hn => by
    have hnX : (n : G) * q * (n : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hXN (Subgroup.mem_inf.mpr ⟨n.2, hn⟩)) q).mp hqX
    have hv : (n : G) * q * (n : G)⁻¹ ∈ Vq G₀ L := hXV hnX
    have e1 : vec ⟨_, hv⟩ = α n • w := hvec_conj n ⟨q, hqV⟩ ⟨_, hv⟩ rfl
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    rcases hdich ⟨_, hnX⟩ with h0 | h1
    · exfalso
      have h0' : vec ⟨_, hv⟩ = 0 := (hvec0 _).mpr (Subgroup.mem_subgroupOf.mp h0)
      rw [e1] at h0'
      apply hw0
      rw [← inv_smul_smul (α n) w, h0', statedSL3_smul_zero]
    · have h1' : vec (⟨_, hv⟩ * ⟨q, hqV⟩) = 0 :=
        (hvec0 _).mpr (Subgroup.mem_subgroupOf.mp h1)
      rw [hvec_mul, e1] at h1'
      rw [eq_neg_of_add_eq_zero_left h1']
      funext i
      exact ZMod.neg_eq_self_mod_two _
  have hRN : R.subgroupOf G₀ ≤ N' := fun r hr =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.le_normalizer (Subgroup.mem_subgroupOf.mp hr))
  have hQR : α.ker ≤ R.subgroupOf G₀ := fun k hk => by
    rw [hQ'] at hk
    exact Subgroup.mem_subgroupOf.mpr (h.pCore_le (Subgroup.mem_subgroupOf.mp hk))
  have hQRidx : α.ker.relIndex (R.subgroupOf G₀) = 4 := by
    rw [hQ', Subgroup.relIndex_subgroupOf h.le]
    exact hTQ
  have hNodd : ¬ 2 ∣ N'.index := hodd.2
  have e1 := Subgroup.relIndex_mul_index hNG₁
  have e2 := Subgroup.relIndex_mul_relIndex α.ker N' G₁' (hQR.trans hRN) hNG₁
  rw [hG₁idx] at e1
  rw [hQG₁idx] at e2
  have hNodd' : ¬ 2 ∣ N'.relIndex G₁' := fun h2 => hNodd (e1 ▸ Dvd.dvd.mul_right h2 7)
  have hcase : N'.relIndex G₁' = 1 ∨ N'.relIndex G₁' = 3 := by
    obtain ⟨m, hm⟩ : ∃ m, N'.relIndex G₁' = m := ⟨_, rfl⟩
    rw [hm] at e2 hNodd' ⊢
    have hm24 : m ∣ 24 := Dvd.intro_left _ e2
    have hmle : m ≤ 24 := Nat.le_of_dvd (by norm_num) hm24
    interval_cases m <;> omega
  have hNG₁eq : N' = G₁' := by
    rcases hcase with h1 | h3
    · exact le_antisymm hNG₁ (Subgroup.relIndex_eq_one.mp h1)
    · exfalso
      rw [h3] at e2
      have h8 : (α.ker.subgroupOf N').index = 8 := by
        show α.ker.relIndex N' = 8
        omega
      have hN2 : IsPGroup 2 ↥N' := by
        have hP : IsPGroup 2 ↥α.ker := by
          rw [hker]
          exact isPGroup_cfsgPCore ↥G₀
        obtain ⟨k, hk⟩ := (hP.comap_of_injective N'.subtype N'.subtype_injective).exists_card_eq
        have hc := Subgroup.card_mul_index (α.ker.subgroupOf N')
        rw [h8] at hc
        change Nat.card ↥(α.ker.comap N'.subtype) * 8 = Nat.card ↥N' at hc
        rw [hk] at hc
        exact IsPGroup.of_card (n := k + 3) (by rw [← hc]; ring)
      have hNmap : N'.map G₀.subtype = G₀ ⊓ Subgroup.normalizer (R : Set G) := by
        rw [hN', Subgroup.subgroupOf_map_subtype, inf_comm]
      have hN2' : IsPGroup 2 ↥(G₀ ⊓ Subgroup.normalizer (R : Set G)) :=
        hNmap ▸ hN2.map G₀.subtype
      have hNR : G₀ ⊓ Subgroup.normalizer (R : Set G) ≤ R :=
        (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer
          hN2').trans hodd.1.ge
      have hN'R : N' = R.subgroupOf G₀ := le_antisymm (fun n hn =>
        Subgroup.mem_subgroupOf.mpr (hNR (Subgroup.mem_inf.mpr ⟨n.2, hn⟩))) hRN
      have h8' : α.ker.relIndex N' = 8 := h8
      rw [hN'R, hQRidx] at h8'
      exact absurd h8' (by norm_num)
  have hG₁N : G₁ = G₀ ⊓ Subgroup.normalizer (R : Set G) := by
    rw [hG₁, ← hNG₁eq, hN', Subgroup.subgroupOf_map_subtype, inf_comm]
  have hRG₁ : R = pCoreOf 2 G₁ := by
    rw [hG₁N]
    exact hodd.1
  have hsurj := surjective_comp_of_case8 h hα hker
  have hZ : Zq G₀ L ≤ Subgroup.centralizer (G₀ : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨ℓ, hℓ⟩ := hsurj (α ⟨g, hg⟩)
    have hk : (ℓ : G)⁻¹ * g ∈ pCoreOf 2 G₀ := by
      have hk' : (⟨(ℓ : G)⁻¹ * g, G₀.mul_mem (G₀.inv_mem (h.L_le ℓ.2)) hg⟩ : ↥G₀) ∈ α.ker := by
        rw [MonoidHom.mem_ker]
        have e : (⟨(ℓ : G)⁻¹ * g, G₀.mul_mem (G₀.inv_mem (h.L_le ℓ.2)) hg⟩ : ↥G₀) =
            (Subgroup.inclusion h.L_le ℓ)⁻¹ * ⟨g, hg⟩ := rfl
        rw [e, map_mul, map_inv]
        rw [MonoidHom.comp_apply] at hℓ
        rw [hℓ, inv_mul_cancel]
      rw [hQ'] at hk'
      exact Subgroup.mem_subgroupOf.mp hk'
    have h1 : (ℓ : G) * z = z * ℓ :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 ℓ ℓ.2
    have h2 : ((ℓ : G)⁻¹ * g) * z = z * ((ℓ : G)⁻¹ * g) :=
      Subgroup.mem_centralizer_iff.mp (A4.centerOf_le_centralizer _
        (A4.omegaOneCenterOf_le_centerOf _ (Subgroup.mem_inf.mp hz).1)) _ hk
    calc g * z = (ℓ : G) * (((ℓ : G)⁻¹ * g) * z) := by group
      _ = (ℓ : G) * (z * ((ℓ : G)⁻¹ * g)) := by rw [h2]
      _ = ((ℓ : G) * z) * ((ℓ : G)⁻¹ * g) := by group
      _ = (z * ℓ) * ((ℓ : G)⁻¹ * g) := by rw [h1]
      _ = z * g := by group
  intro S hS hRS
  have hSG : S ≤ G₀ := hS.1
  have hSR : R.relIndex S = 2 := by
    have hRidx : (R.subgroupOf G₀).index = 42 := by
      have e := Subgroup.relIndex_mul_index hQR
      rw [hQRidx, hQidx] at e
      omega
    have hRS' : R.subgroupOf G₀ ≤ S.subgroupOf G₀ := fun r hr =>
      Subgroup.mem_subgroupOf.mpr (hRS (Subgroup.mem_subgroupOf.mp hr))
    have e := Subgroup.relIndex_mul_index hRS'
    rw [hRidx, Subgroup.relIndex_subgroupOf hSG] at e
    have hSodd : ¬ 2 ∣ (S.subgroupOf G₀).index := hS.2.2
    obtain ⟨j, hj⟩ : ∃ j, R.relIndex S = 2 ^ j := by
      have hd : R.relIndex S ∣ Nat.card ↥S := Subgroup.index_dvd_card (R.subgroupOf S)
      obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
      rw [hk] at hd
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      exact ⟨j, hj⟩
    rw [hj] at e ⊢
    rcases j with _ | _ | j
    · rw [pow_zero, one_mul] at e
      exact absurd (e ▸ (by norm_num : 2 ∣ 42)) hSodd
    · rfl
    · exfalso
      have h4 : 2 ^ 2 ∣ 2 ^ (j + 2) * (S.subgroupOf G₀).index :=
        (Nat.pow_dvd_pow 2 (by omega)).mul_right _
      rw [e] at h4
      norm_num at h4
  have hSN : S ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRS).mp
      (Subgroup.normal_of_index_eq_two (H := R.subgroupOf S) hSR)
  have hSG₁ : S ≤ G₁ := by
    rw [hG₁N]
    exact le_inf hSG hSN
  have hZS : omegaOneCenterOf S ≤ centerOf G₀ := by
    have hQS : pCoreOf 2 G₀ ≤ S := h.pCore_le.trans hRS
    have hZN : Zq G₀ L ≤ Subgroup.normalizer (Vq G₀ L : Set G) := Zq_le.trans hMV
    unfold omegaOneCenterOf omegaOneOf
    rw [Subgroup.closure_le]
    rintro x ⟨⟨hxS, hxC⟩, hx2⟩
    have hxCQ : x ∈ Subgroup.centralizer (pCoreOf 2 G₀ : Set G) := Subgroup.centralizer_le hQS hxC
    have hxQ : x ∈ pCoreOf 2 G₀ := h.charTwo ⟨hSG hxS, hxCQ⟩
    have hxX : x ∈ Xq G₀ := Subgroup.subset_closure ⟨⟨hxQ, hxCQ⟩, hx2⟩
    have hxZV : x ∈ Zq G₀ L ⊔ Vq G₀ L := by
      rw [hVU, ← hX]
      exact hxX
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZN] at hxZV
    obtain ⟨z, hz, v, hv, rfl⟩ := hxZV
    have hzC : z ∈ Subgroup.centralizer (G₀ : Set G) := hZ hz
    have hvS : v ∈ Subgroup.centralizer (S : Set G) := by
      have hzS : z ∈ Subgroup.centralizer (S : Set G) := Subgroup.centralizer_le hSG hzC
      have hv' : v = z⁻¹ * (z * v) := by group
      rw [hv']
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzS) hxC
    have hvC : v ∈ CV := by
      rw [← hSyl S hS]
      exact ⟨hv, hvS⟩
    exact ⟨Subgroup.mul_mem _ (Zq_le hz) (Vq_le h.L_le hv),
      Subgroup.mul_mem _ hzC (Subgroup.mem_inf.mp hvC).2⟩
  refine ⟨hZS, q, G₁, hqV, ?_, hmemG₁, hG₁rel, hSG₁, hRG₁⟩
  rw [hCQ]
  exact hqCV

end CFSG.Quasithin.MS93
