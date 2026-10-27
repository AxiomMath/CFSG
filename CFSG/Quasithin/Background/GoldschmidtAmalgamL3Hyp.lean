module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamNSetup
public import CFSG.Quasithin.Background.GoldschmidtAmalgamF9V
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Bound
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D}

theorem oTwoRes_oTwoRes (X : Subgroup D) : oTwoRes (oTwoRes X) = oTwoRes X := by
  refine le_antisymm (oTwoRes_le _) ((Subgroup.closure_le _).mpr fun x hx => ?_)
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.2⟩

theorem pCoreOf_pCoreOf [Finite D] (X : Subgroup D) : pCoreOf 2 (pCoreOf 2 X) = pCoreOf 2 X :=
  le_antisymm (pCoreOf_le 2 _)
    (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer (pCoreOf_isPGroup 2 X))

theorem mem_centralizer_zpowers_of_mul_comm {y z : D} (hc : y * z = z * y) :
    y ∈ Subgroup.centralizer (Subgroup.zpowers z : Set D) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact ((Commute.zpow_right (show Commute y z from hc) k).symm).eq

theorem centralizerMod_le_normalizer_of_le {V₁ H Vp : Subgroup D} (hV : V₁ ≤ Vp) :
    centralizerMod V₁ H Vp ≤ H ⊓ Subgroup.normalizer (Vp : Set D) := by
  intro x hx
  have key : ∀ y ∈ centralizerMod V₁ H Vp, ∀ v ∈ Vp, y * v * y⁻¹ ∈ Vp := by
    intro y hy v hv
    have h1 := hy.2.2 v hv
    have e : y * v * y⁻¹ = (y * v * y⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact Vp.mul_mem (hV h1) hv
  refine ⟨hx.1, Subgroup.mem_normalizer_iff.mpr fun v => ⟨key x hx v, fun hv => ?_⟩⟩
  have := key x⁻¹ ((centralizerMod V₁ H Vp).inv_mem hx) _ hv
  simpa [mul_assoc] using this

theorem exists_order_three_of_normal_not_le [Finite D] {H N : Subgroup D}
    (hq : Nonempty (↥H ⧸ CFSG.Open.pCore 2 ↥H ≃* Equiv.Perm (Fin 3))) (hNH : N ≤ H)
    (hH : H ≤ Subgroup.normalizer (N : Set D)) (hN : ¬ N ≤ pCoreOf 2 H) :
    ∃ x ∈ N, orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨π, hπ, hker⟩ := GoldAmN.exists_hom_perm_three H hq
  obtain ⟨n, hnN, hnQ⟩ := IsConcreteLE.not_le_iff_exists.mp hN
  have hnH : n ∈ H := hNH hnN
  have hπn : π ⟨n, hnH⟩ ≠ 1 := fun e =>
    hnQ ((GoldAmN.mem_pCoreOf_iff hnH).mpr (by rw [← hker]; exact e))
  obtain ⟨b, hb3, hb1⟩ := GoldAmN.perm3_exists_order_three_prod (π ⟨n, hnH⟩) hπn
  obtain ⟨g, rfl⟩ := hπ b
  have hgn : (g : D) * n * (g : D)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hH g.2) n).mp hnN
  have hcN : n * ((g : D) * n * (g : D)⁻¹) ∈ N := N.mul_mem hnN hgn
  have hcH : n * ((g : D) * n * (g : D)⁻¹) ∈ H :=
    H.mul_mem hnH (H.mul_mem (H.mul_mem g.2 hnH) (H.inv_mem g.2))
  set c : ↥H := ⟨n * ((g : D) * n * (g : D)⁻¹), hcH⟩ with hc
  have hπc : π c = π ⟨n, hnH⟩ * (π g * π ⟨n, hnH⟩ * (π g)⁻¹) := by
    have : c = ⟨n, hnH⟩ * (g * ⟨n, hnH⟩ * g⁻¹) := rfl
    rw [this]; simp
  have hord : orderOf (π c) = 3 := by
    rw [hπc]; exact orderOf_eq_prime hb3 hb1
  have hdvd : 3 ∣ orderOf c := hord ▸ orderOf_map_dvd π c
  refine ⟨((c ^ (orderOf c / 3) : ↥H) : D), ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact N.pow_mem hcN _
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (orderOf_pos c).ne' hdvd

section Setup

variable [Finite D] {z : D} {V : Subgroup D}

omit [Finite D] in
theorem card_zpowers_eq_two (hn : IsNaturalAt A (A ⊓ B) z V) :
    Nat.card (Subgroup.zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hn.z_sq hn.z_ne

theorem oTwoRes_sup_inf_eq (h : GoldHyp A B) : oTwoRes A ⊔ (A ⊓ B) = A := by
  obtain ⟨x, hxA, hx3⟩ := h.vertex_left.exists_order_three
  have hxo : x ∈ oTwoRes A :=
    Subgroup.subset_closure ⟨hxA, 3, by decide, by rw [← hx3]; exact pow_orderOf_eq_one x⟩
  apply le_antisymm
  · exact sup_le (oTwoRes_le A) inf_le_left
  · have h1 := GoldAmN.inf_sup_zpowers_eq_right_vTriple
      h.symm.amalgam.toIsGoldschmidtVTriple hxA hx3
    rw [inf_comm] at h1
    exact h1.symm.le.trans
      (sup_le le_sup_right ((Subgroup.zpowers_le.mpr hxo).trans le_sup_left))

theorem inf_normalizer_zpowers_le (h : GoldHyp A B) (hn : IsNaturalAt A (A ⊓ B) z V) :
    A ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set D) ≤ A ⊓ B := by
  have hTM : A ⊓ B ≤ A ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set D) := by
    refine le_inf inf_le_left (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
    intro t ht
    exact mem_centralizer_zpowers_of_mul_comm
      (Subgroup.mem_centralizer_iff.mp hn.z_mem.2 t ht)
  have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hTM
    (inf_le_left : A ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set D) ≤ A)
  rw [h.relIndex_left] at h1
  have hb : (A ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set D)).relIndex A ∣ 3 :=
    ⟨(A ⊓ B).relIndex (A ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set D)), by
      rw [← h1]; ring⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hb with hb1 | hb3
  · exfalso
    apply hn.not_normalizes
    intro a ha
    exact ((Subgroup.relIndex_eq_one.mp hb1) ha).2
  · rw [hb3] at h1
    exact Subgroup.relIndex_eq_one.mp (by omega)

theorem ker_le_pCoreOf (h : GoldHyp A B) (hn : IsNaturalAt A (A ⊓ B) z V) :
    coreIn (centralizerMod (Subgroup.zpowers z) B V) B ≤ pCoreOf 2 B := by
  intro x hx
  by_contra hxQ
  set N := coreIn (centralizerMod (Subgroup.zpowers z) B V) B with hNdef
  have hNB : N ≤ B := coreIn_le_left _ _
  have hBN : B ≤ Subgroup.normalizer (N : Set D) := le_normalizer_coreIn _ _
  have hNK : N ≤ centralizerMod (Subgroup.zpowers z) B V := coreIn_le_right _ _
  obtain ⟨y, hyN, hy3⟩ := exists_order_three_of_normal_not_le h.amalgam.quotient₂ hNB hBN
    (fun hle => hxQ (hle hx))
  have hzV : Subgroup.zpowers z ≤ V := Subgroup.zpowers_le.mpr hn.z_mem_V
  have hyV : y ∈ Subgroup.normalizer (V : Set D) :=
    (centralizerMod_le_normalizer_of_le hzV (hNK hyN)).2
  have hTV : A ⊓ B ≤ Subgroup.normalizer (V : Set D) := inf_le_left.trans hn.reduced.2.1
  have hBV : B ≤ Subgroup.normalizer (V : Set D) :=
    GoldAmN.le_normalizer_of_mem_vTriple h.amalgam.toIsGoldschmidtVTriple (hNB hyN) hy3 hTV hyV
  have hVT : V ≤ A ⊓ B := hn.le_pCoreOf.trans h.pCoreOf_left_le
  exact hn.natural.ne_bot (h.eq_bot_of_normalizes hn.reduced.2.1 hBV hVT)

theorem hypF91V_of_labelled (h : GoldHyp A B) (hn : IsNaturalAt A (A ⊓ B) z V)
    (hz : ∀ y ∈ B, y * z * y⁻¹ = z) (hU : IsElemAbelian 2 (conjClosure V B)) :
    HypF91V (A ⊓ B) V (oTwoRes A) (Subgroup.zpowers z) V B where
  sylow_H := h.isSylowTwoOf_right
  sylow_LT := by rw [oTwoRes_sup_inf_eq h]; exact h.isSylowTwoOf_left
  elemAbelian := hn.reduced.2.2.1
  normalizes_L := inf_le_left.trans (le_normalizer_oTwoRes A)
  oTwoRes_eq := oTwoRes_oTwoRes A
  charTwo_L := A4.charTwo_of_normal (oTwoRes_le A) (le_normalizer_oTwoRes A) h.charTwo₁
  reduced := by rw [oTwoRes_sup_inf_eq h]; exact hn.reduced
  cT := by
    rw [oTwoRes_sup_inf_eq h, hn.cT, hn.centralizer_eq, pCoreOf_pCoreOf]
  card_V₁ := card_zpowers_eq_two hn
  V₁_lt_Vp := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr hn.z_mem_V) fun e => ?_
    have h4 := hn.card_eq
    rw [← e, card_zpowers_eq_two hn] at h4
    omega
  Vp_le_V := le_rfl
  T_normalizes_V₁ := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro t ht
    exact mem_centralizer_zpowers_of_mul_comm
      (Subgroup.mem_centralizer_iff.mp hn.z_mem.2 t ht)
  H_le_centralizer := fun y hy =>
    mem_centralizer_zpowers_of_mul_comm (mul_eq_of_conj_eq (hz y hy))
  L₁T_le_H := by
    have hL₁ : L₁Of (oTwoRes A) (Subgroup.zpowers z) ≤ A ⊓ B :=
      (oTwoRes_le _).trans ((inf_le_inf_right _ (oTwoRes_le A)).trans
        (inf_normalizer_zpowers_le h hn))
    exact sup_le (hL₁.trans inf_le_right) inf_le_right
  charTwo_H := h.charTwo₂
  ker_le := ker_le_pCoreOf h hn
  L₁T_normalizes_Vp := by
    have hL₁ : L₁Of (oTwoRes A) (Subgroup.zpowers z) ≤ A ⊓ B :=
      (oTwoRes_le _).trans ((inf_le_inf_right _ (oTwoRes_le A)).trans
        (inf_normalizer_zpowers_le h hn))
    exact sup_le (hL₁.trans (inf_le_left.trans hn.reduced.2.1))
      (inf_le_left.trans hn.reduced.2.1)
  irred := fun W h1 h2 _ => by
    have c1 : Nat.card (Subgroup.zpowers z) ∣ Nat.card W := Subgroup.card_dvd_of_le h1
    have c2 : Nat.card W ∣ Nat.card V := Subgroup.card_dvd_of_le h2
    rw [card_zpowers_eq_two hn] at c1
    rw [hn.card_eq] at c2
    have hle : Nat.card W ≤ 4 := Nat.le_of_dvd (by norm_num) c2
    have hpos : 0 < Nat.card W := Nat.card_pos
    have hW : Nat.card W = 2 ∨ Nat.card W = 4 := by omega
    rcases hW with hW | hW
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge h1 (by rw [hW, card_zpowers_eq_two hn])).symm
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge h2 (by rw [hW, hn.card_eq]))
  normalizer_le := inf_le_right
  o2_trivial := by rw [oTwoRes_sup_inf_eq h]; exact h.amalgamHyp.o2_trivial
  weak_e := fun g hg _ _ _ => by
    have hgU : conjSub g⁻¹ V ≤ conjClosure V B := HypF91.conjSub_le_conjClosure (B.inv_mem hg)
    have hc : ⁅V, conjSub g⁻¹ V⁆ = ⊥ := by
      refine le_bot_iff.mp ((Subgroup.commutator_mono (le_conjClosure V B) hgU).trans ?_)
      rw [commutator_self_eq_bot hU]
    exact ⟨hc, by rw [Subgroup.commutator_comm]; exact hc⟩

theorem three_le_critDist_iff (h : GoldHyp A B) (hn : IsNaturalAt A (A ⊓ B) z V)
    (hz : ∀ y ∈ B, y * z * y⁻¹ = z) :
    3 ≤ critDist (A ⊔ B) A B V ↔ IsElemAbelian 2 (conjClosure V B) := by
  have hVQ : V ≤ pCoreOf 2 B := hn.le_pCoreOf_of_centralizes h hz
  have h2 : 2 ≤ critDist (A ⊔ B) A B V := (two_le_critDist_iff h hn).mpr hVQ
  constructor
  · intro h3
    rcases critDist_dichotomy h hn hVQ with hb | ⟨-, hU⟩
    · omega
    · exact hU
  · intro hU
    by_contra hlt
    have hb : critDist (A ⊔ B) A B V = 2 := by omega
    have hc := (labelled_two_structure h hn hz hb).2.2.2
    rw [commutator_self_eq_bot hU] at hc
    apply hn.z_ne
    have hzmem : z ∈ (⊥ : Subgroup D) := by rw [hc]; exact Subgroup.mem_zpowers z
    simpa using hzmem

end Setup

structure GoldHyp3 (A B : Subgroup D) (z : D) (V : Subgroup D) : Prop where
  gold : GoldHyp A B
  natural : IsNaturalAt A (A ⊓ B) z V
  central : ∀ y ∈ B, y * z * y⁻¹ = z
  abelian : IsElemAbelian 2 (conjClosure V B)

namespace GoldHyp3

variable [Finite D] {z : D} {V : Subgroup D}

theorem hypF91V (h : GoldHyp3 A B z V) :
    HypF91V (A ⊓ B) V (oTwoRes A) (Subgroup.zpowers z) V B :=
  hypF91V_of_labelled h.gold h.natural h.central h.abelian

theorem three_le_critDist (h : GoldHyp3 A B z V) : 3 ≤ critDist (A ⊔ B) A B V :=
  (three_le_critDist_iff h.gold h.natural h.central).mpr h.abelian

theorem le_pCoreOf_right (h : GoldHyp3 A B z V) : V ≤ pCoreOf 2 B :=
  h.natural.le_pCoreOf_of_centralizes h.gold h.central

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
