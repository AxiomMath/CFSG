module

public import CFSG.Quasithin.Background.Harris.R1.AbelIndex
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Background.Harris.R1.Defs

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_self_mem_of_closure {W Zs : Subgroup G} {s : Set G} (hW : W = Subgroup.closure s)
    (hs : ∀ g ∈ s, g * g = 1) (hc : ⁅W, W⁆ ≤ Zs) : ∀ w ∈ W, w * w ∈ Zs := by
  intro w hw
  have hw' : w ∈ Subgroup.closure s := hW ▸ hw
  induction hw' using Subgroup.closure_induction with
  | mem x hx => rw [hs x hx]; exact Zs.one_mem
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxW : x ∈ W := hW ▸ hx
    have hyW : y ∈ W := hW ▸ hy
    have hcm := hc (Subgroup.commutator_mem_commutator (W.inv_mem hxW) hyW)
    rw [commutatorElement_def] at hcm
    have e : x * y * (x * y) = (x * x) * (x⁻¹ * y * x⁻¹⁻¹ * y⁻¹) * (y * y) := by group
    rw [e]
    exact Zs.mul_mem (Zs.mul_mem (ihx hxW) hcm) (ihy hyW)
  | inv x hx ihx =>
    have hxW : x ∈ W := hW ▸ hx
    have e : x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
    rw [e]
    exact Zs.inv_mem (ihx hxW)

omit [Finite G] in
theorem commutator_mul_central {a b za zb : G} (h1 : Commute za a) (h2 : Commute za b)
    (h3 : Commute za zb) (h4 : Commute zb a) (h5 : Commute zb b) :
    za * a * (zb * b) * (za * a)⁻¹ * (zb * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have e1 : za * a * (zb * b) * (za * a)⁻¹ * (zb * b)⁻¹ = a * zb * b * a⁻¹ * b⁻¹ * zb⁻¹ := by
    calc za * a * (zb * b) * (za * a)⁻¹ * (zb * b)⁻¹
        = (za * (a * zb * b)) * (a⁻¹ * za⁻¹) * (b⁻¹ * zb⁻¹) := by group
      _ = ((a * zb * b) * za) * (a⁻¹ * za⁻¹) * (b⁻¹ * zb⁻¹) := by
          rw [((h1.mul_right h3).mul_right h2).eq]
      _ = (a * zb * b) * (za * a⁻¹) * za⁻¹ * (b⁻¹ * zb⁻¹) := by group
      _ = (a * zb * b) * (a⁻¹ * za) * za⁻¹ * (b⁻¹ * zb⁻¹) := by rw [h1.inv_right.eq]
      _ = a * zb * b * a⁻¹ * b⁻¹ * zb⁻¹ := by group
  rw [e1]
  calc a * zb * b * a⁻¹ * b⁻¹ * zb⁻¹ = a * (zb * (b * a⁻¹ * b⁻¹)) * zb⁻¹ := by group
    _ = a * ((b * a⁻¹ * b⁻¹) * zb) * zb⁻¹ := by
        rw [((h5.mul_right h4.inv_right).mul_right h5.inv_right).eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem conjOTwoQuot_eq_one_of_mem {K1 S : Subgroup G}
    (hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G)) {g : ↥(K1 ⊔ S)}
    (hg : (g : G) ∈ pCoreOf 2 (K1 ⊔ S)) : conjOTwoQuot K1 (K1 ⊔ S) hN g = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [conjOTwoQuot_apply_mk, MulAut.one_apply, QuotientGroup.eq]
    have hQn := le_normalizer_pCoreOf 2 (K1 ⊔ S) g.2
    have h1 : (g : G) * ((k : G)⁻¹ * (g : G)⁻¹ * k) ∈ pCoreOf 2 (K1 ⊔ S) := by
      have hk : (k : G)⁻¹ ∈ K1 ⊔ S := Subgroup.mem_sup_left (K1.inv_mem k.2)
      have h2 := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 (K1 ⊔ S) hk) _).mp ((pCoreOf 2 (K1 ⊔ S)).inv_mem hg)
      have e : (k : G)⁻¹ * (g : G)⁻¹ * (k : G)⁻¹⁻¹ = (k : G)⁻¹ * (g : G)⁻¹ * k := by group
      rw [e] at h2
      exact (pCoreOf 2 (K1 ⊔ S)).mul_mem hg h2
    have hK : (g : G) * (k : G)⁻¹ * (g : G)⁻¹ * k ∈ K1 :=
      K1.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN g.2) _).mp (K1.inv_mem k.2)) k.2
    have hle : K1 ⊓ pCoreOf 2 (K1 ⊔ S) ≤ pCoreOf 2 K1 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine le_pCoreOf_of_le_normalizer inf_le_left (fun k' hk' => ?_)
        ((pCoreOf_isPGroup 2 (K1 ⊔ S)).to_le inf_le_right)
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · rintro ⟨hu1, hu2⟩
        exact ⟨K1.mul_mem (K1.mul_mem hk' hu1) (K1.inv_mem hk'),
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (K1 ⊔ S)
            (Subgroup.mem_sup_left hk')) u).mp hu2⟩
      · rintro ⟨hu1, hu2⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (K1 ⊔ S)
            (Subgroup.mem_sup_left hk')) u).mpr hu2⟩
        have := K1.mul_mem (K1.mul_mem (K1.inv_mem hk') hu1) hk'
        simpa [mul_assoc] using this
    have hmem : (g : G) * (k : G)⁻¹ * (g : G)⁻¹ * k ∈ pCoreOf 2 K1 :=
      hle ⟨hK, by simpa [mul_assoc] using h1⟩
    obtain ⟨u, hu, hue⟩ := hmem
    have hu' : u = (⟨(g : G) * k * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hN g.2) k).mp k.2⟩ : ↥K1)⁻¹ * k := by
      apply Subtype.ext
      simp only [Subgroup.coe_subtype] at hue
      simp [hue, mul_assoc]
    rw [← hu']
    exact hu

omit [Finite G] in
theorem mul_comm_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem abelIndex_holds : AbelIndexStmt := by
  intro G _ _ K1 L2 S Zs h _ hna
  have hRO : RankOneListedFacts.{0} := rankOneListedFacts
  have hyp := F112J2.amalgamHypV_of_setting hRO h
  have hS3 := F112J2.isNaturalS3_of_setting hRO h
  have hb := F112J2.critDist_eq_two_of_setting hRO h hna
  have hcard : Nat.card ↥(conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G)) = 2 :=
    F112W.card_inf_centralizer_T hyp hS3
  have hZeq : conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G) = Zs :=
    (Subgroup.eq_of_le_of_card_ge (le_inf (le_conjClosure Zs L2) h.Z_cent_S)
      (by rw [hcard, h.card_Z])).symm
  have hNZ : K1 ⊔ S ≤ Subgroup.normalizer
      ((conjClosure Zs L2 ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
    rw [hZeq]
    exact (sup_le h.K1_cent_Z (F112J2.S_le_centralizer_Z h)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hWQ : ⁅vBeta K1 L2 S Zs, pCoreOf 2 (K1 ⊔ S)⁆ = Zs :=
    (F112W.commutator_conjClosure_pCoreOf hyp hS3 hb hNZ).trans hZeq
  have hWW : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ = Zs :=
    (F112W.commutator_conjClosure_self hyp hS3 hb hNZ).trans hZeq
  obtain ⟨-, -, hidx, x, -, hV'W, -, -, -, hcomm, hVV', hc2, -⟩ :=
    F112W.critDist_two_structure hyp hS3 hb
  have hQaS : pCoreOf 2 (L2 ⊔ S) ≤ S := isSylowTwoOf_pCoreOf_le hyp.sylow₁
  have hVQb : conjClosure Zs L2 ≤ pCoreOf 2 (K1 ⊔ S) := h.V_le
  have hVab := hyp.elemAbelian
  have hV'ab : IsElemAbelian 2 (conjSub x (conjClosure Zs L2)) := isElemAbelian_conjSub hVab
  have hVcard : Nat.card ↥(conjClosure Zs L2) = 4 := h.V_card
  have hVc : ∀ v ∈ conjClosure Zs L2, ∀ q ∈ pCoreOf 2 (L2 ⊔ S), v * q = q * v := by
    have hle : conjClosure Zs L2 ≤ Subgroup.centralizer (pCoreOf 2 (L2 ⊔ S) : Set G) := by
      apply conjClosure_le
      intro l hl z hz
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : l⁻¹ * q * l⁻¹⁻¹ ∈ pCoreOf 2 (L2 ⊔ S) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (L2 ⊔ S)
          (Subgroup.mem_sup_left (L2.inv_mem hl))) q).mp hq
      rw [inv_inv] at hq'
      have h1 : (l⁻¹ * q * l) * z = z * (l⁻¹ * q * l) :=
        Subgroup.mem_centralizer_iff.mp (h.Z_cent_S hz) _ (hQaS hq')
      calc q * (l * z * l⁻¹) = l * ((l⁻¹ * q * l) * z) * l⁻¹ := by group
        _ = l * (z * (l⁻¹ * q * l)) * l⁻¹ := by rw [h1]
        _ = l * z * l⁻¹ * q := by group
    intro v hv q hq
    exact (Subgroup.mem_centralizer_iff.mp (hle hv) q hq).symm
  have hCV : ∀ v ∈ conjClosure Zs L2,
      (∀ u ∈ conjSub x (conjClosure Zs L2), v * u = u * v) → v ∈ Zs := by
    intro v hv hvc
    by_contra hvZ
    let C := conjClosure Zs L2 ⊓ Subgroup.centralizer (conjSub x (conjClosure Zs L2) : Set G)
    have hZC : Zs ≤ C := by
      rw [← hZeq, ← hVV']
      rintro u ⟨hu1, hu2⟩
      exact ⟨hu1, Subgroup.mem_centralizer_iff.mpr fun w hw =>
        mul_comm_of_isElemAbelian hV'ab hw hu2⟩
    have hvC : v ∈ C := ⟨hv, Subgroup.mem_centralizer_iff.mpr fun u hu => (hvc u hu).symm⟩
    have hCV4 : Nat.card ↥C ∣ 4 := hVcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2C : 2 ∣ Nat.card ↥C := h.card_Z ▸ Subgroup.card_dvd_of_le hZC
    have hC2 : Nat.card ↥C ≠ 2 := by
      intro hC
      exact hvZ ((Subgroup.eq_of_le_of_card_ge hZC (by rw [hC, h.card_Z])) ▸ hvC)
    have hC4 : Nat.card ↥C = 4 := by
      have hpos : 0 < Nat.card ↥C := Nat.card_pos
      have := Nat.le_of_dvd (by norm_num) hCV4
      interval_cases hc : Nat.card ↥C <;> simp_all
    have hCeq : C = conjClosure Zs L2 :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hC4, hVcard])
    have hbot : ⁅conjClosure Zs L2, conjSub x (conjClosure Zs L2)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun v hv => (hCeq.symm.le hv).2
    rw [hcomm] at hbot
    rw [hbot, Subgroup.card_bot] at hc2
    omega
  obtain ⟨y, hyL, hyN⟩ : ∃ y ∈ L2, y ∉ Subgroup.normalizer (Zs : Set G) := by
    by_contra hcon
    exact h.Z_not_norm fun y hy => by_contra fun hn => hcon ⟨y, hy, hn⟩
  have hZ'V : conjSub y Zs ≤ conjClosure Zs L2 := by
    intro z hz
    rw [mem_conjSub] at hz
    have := mem_conjClosure (Z := Zs) (H := L2) hyL hz
    simpa [mul_assoc] using this
  have hZ'ne : conjSub y Zs ≠ Zs := by
    intro he
    apply hyN
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [← he]
      exact mul_mem_conjSub hz
    · intro hz
      rw [← he, mem_conjSub] at hz
      simpa [mul_assoc] using hz
  have hZ'card : Nat.card ↥(conjSub y Zs) = 2 := (card_conjSub y Zs).trans h.card_Z
  obtain ⟨z', hz', hz'Z⟩ : ∃ z' ∈ conjSub y Zs, z' ∉ Zs := by
    by_contra hcon
    exact hZ'ne (Subgroup.eq_of_le_of_card_ge (fun z hz => by_contra fun hn => hcon ⟨z, hz, hn⟩)
      (by rw [hZ'card, h.card_Z]))
  have hcommy : ⁅conjSub y (vBeta K1 L2 S Zs), conjSub y (vBeta K1 L2 S Zs)⁆ = conjSub y Zs := by
    rw [conjSub, conjSub, ← Subgroup.map_commutator, hWW]
  have hA : ∀ a ∈ conjSub y (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S) ⊓ pCoreOf 2 (K1 ⊔ S),
      ∀ b ∈ conjSub y (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S) ⊓ pCoreOf 2 (K1 ⊔ S),
      a * b = b * a := by
    rintro a ⟨⟨haW, haQ⟩, haR⟩ b ⟨⟨hbW, hbQ⟩, hbR⟩
    have hab : a * b * a⁻¹ * b⁻¹ ∈ conjSub y Zs := by
      rw [← hcommy]
      have := Subgroup.commutator_mem_commutator haW hbW
      rwa [commutatorElement_def] at this
    have hcen : ∀ w ∈ vBeta K1 L2 S Zs,
        w * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * w := by
      intro w hw
      have hza : w * a * w⁻¹ * a⁻¹ ∈ Zs := by
        rw [← hWQ]
        have := Subgroup.commutator_mem_commutator hw haR
        rwa [commutatorElement_def] at this
      have hzb : w * b * w⁻¹ * b⁻¹ ∈ Zs := by
        rw [← hWQ]
        have := Subgroup.commutator_mem_commutator hw hbR
        rwa [commutatorElement_def] at this
      have hzaV := le_conjClosure Zs L2 hza
      have hzbV := le_conjClosure Zs L2 hzb
      have key := commutator_mul_central (a := a) (b := b)
        (za := w * a * w⁻¹ * a⁻¹) (zb := w * b * w⁻¹ * b⁻¹)
        (hVc _ hzaV a haQ) (hVc _ hzaV b hbQ) (mul_comm_of_isElemAbelian hVab hzaV hzbV)
        (hVc _ hzbV a haQ) (hVc _ hzbV b hbQ)
      have e1 : w * a * w⁻¹ * a⁻¹ * a = w * a * w⁻¹ := by group
      have e2 : w * b * w⁻¹ * b⁻¹ * b = w * b * w⁻¹ := by group
      rw [e1, e2] at key
      calc w * (a * b * a⁻¹ * b⁻¹)
          = (w * a * w⁻¹) * (w * b * w⁻¹) * (w * a * w⁻¹)⁻¹ * (w * b * w⁻¹)⁻¹ * w := by group
        _ = (a * b * a⁻¹ * b⁻¹) * w := by rw [key]
    by_contra hne
    have hc1 : a * b * a⁻¹ * b⁻¹ ≠ 1 := by
      intro h1
      apply hne
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    have hord : orderOf (a * b * a⁻¹ * b⁻¹) = 2 := by
      have hdvd : orderOf (⟨_, hab⟩ : ↥(conjSub y Zs)) ∣ 2 := hZ'card ▸ orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hc1
      · exact h1
    have hzp : Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) = conjSub y Zs :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hab)
        (by rw [hZ'card, Nat.card_zpowers, hord])
    have hz'c : ∀ w ∈ vBeta K1 L2 S Zs, w * z' = z' * w := by
      intro w hw
      rw [← hzp] at hz'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
      exact ((Commute.zpow_right (hcen w hw) k)).eq
    exact hz'Z (hCV z' (hZ'V hz') fun u hu => (hz'c u (hV'W hu)).symm)
  have hyQ : y ∈ Subgroup.normalizer (pCoreOf 2 (L2 ⊔ S) : Set G) :=
    le_normalizer_pCoreOf 2 (L2 ⊔ S) (Subgroup.mem_sup_left hyL)
  have hQay : conjSub y (pCoreOf 2 (L2 ⊔ S)) = pCoreOf 2 (L2 ⊔ S) := by
    ext q
    rw [mem_conjSub]
    have hyQ' : y⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 (L2 ⊔ S) : Set G) :=
      Subgroup.inv_mem _ hyQ
    have := (Subgroup.mem_normalizer_iff.mp hyQ' q)
    rw [inv_inv] at this
    exact this.symm
  have hXeq : conjSub y (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S) =
      conjSub y (vBeta K1 L2 S Zs ⊓ pCoreOf 2 (L2 ⊔ S)) := by
    conv_lhs => rw [← hQay]
    rw [conjSub, conjSub, conjSub, Subgroup.map_inf_eq _ _ _ (MulEquiv.injective _)]
  have hW2 : Nat.card ↥(vBeta K1 L2 S Zs) =
      2 * Nat.card ↥(conjSub y (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S)) := by
    rw [hXeq, card_conjSub]
    have := Subgroup.relIndex_mul_card (H := pCoreOf 2 (L2 ⊔ S)) (K := vBeta K1 L2 S Zs)
    rw [show (pCoreOf 2 (L2 ⊔ S)).relIndex (vBeta K1 L2 S Zs) = 2 from hidx, inf_comm] at this
    omega
  have hN1 : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G) :=
    sup_le Subgroup.le_normalizer h.hyp.h1.normalizes
  have hXle : conjSub y (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S) ≤ K1 ⊔ S :=
    inf_le_right.trans (hQaS.trans le_sup_right)
  let ψ : ↥(conjSub y (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S)) →* MulAut (OTwoQuot K1) :=
    (conjOTwoQuot K1 (K1 ⊔ S) hN1).comp (Subgroup.inclusion hXle)
  have hsq : ∀ u ∈ conjSub y (vBeta K1 L2 S Zs), u * u ∈ conjSub y Zs := by
    have hW : vBeta K1 L2 S Zs = Subgroup.closure
        {g | ∃ h ∈ K1 ⊔ S, ∃ v ∈ conjClosure Zs L2, h * v * h⁻¹ = g} := rfl
    have hgen : ∀ g ∈ {g | ∃ h ∈ K1 ⊔ S, ∃ v ∈ conjClosure Zs L2, h * v * h⁻¹ = g},
        g * g = 1 := by
      rintro _ ⟨k, -, v, hv, rfl⟩
      have hv2 : v ^ 2 = 1 := hVab.2 v hv
      rw [pow_two] at hv2
      calc k * v * k⁻¹ * (k * v * k⁻¹) = k * (v * v) * k⁻¹ := by group
        _ = 1 := by rw [hv2]; group
    have hsqW := mul_self_mem_of_closure hW hgen hWW.le
    intro u hu
    rw [mem_conjSub] at hu
    have := mul_mem_conjSub (g := y) (hsqW _ hu)
    have e : y * (y⁻¹ * u * y * (y⁻¹ * u * y)) * y⁻¹ = u * u := by group
    rwa [e] at this
  refine ⟨conjSub y⁻¹ (conjSub y (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S) ⊓ pCoreOf 2 (K1 ⊔ S)),
    ?_, ?_, ψ.range, ?_, ?_⟩
  · intro u hu
    rw [mem_conjSub, inv_inv] at hu
    have := mem_conjSub.mp hu.1.1
    simpa [mul_assoc] using this
  · intro u hu v hv
    rw [mem_conjSub, inv_inv] at hu hv
    have := hA _ hu _ hv
    have e : y * u * y⁻¹ * (y * v * y⁻¹) = y * (u * v) * y⁻¹ := by group
    have e' : y * v * y⁻¹ * (y * u * y⁻¹) = y * (v * u) * y⁻¹ := by group
    rw [e, e'] at this
    simpa using this
  · rintro _ ⟨u, rfl⟩
    rw [← map_mul]
    apply conjOTwoQuot_eq_one_of_mem hN1
    exact hVQb (hZ'V (hsq _ u.2.1))
  ·
    have hker : Nat.card ψ.ker ≤
        Nat.card ↥(conjSub y⁻¹ (conjSub y (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S) ⊓
          pCoreOf 2 (K1 ⊔ S))) := by
      rw [card_conjSub]
      refine Nat.card_le_card_of_injective
        (fun k => ⟨((k : ↥(conjSub y (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S))) : G),
          ⟨(k : ↥(conjSub y (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S))).2, ?_⟩⟩) ?_
      · have hk := MonoidHom.mem_ker.mp k.2
        exact mem_pCoreOf_of_conjOTwoQuot_eq_one (hyp.sylow₁.2.1) hN1
          (hQaS (k : ↥(conjSub y (vBeta K1 L2 S Zs) ⊓ pCoreOf 2 (L2 ⊔ S))).2.2) hk
      · intro k₁ k₂ hk
        have h1 := congrArg Subtype.val hk
        apply Subtype.ext
        apply Subtype.ext
        exact h1
    have hkr := Subgroup.card_ker_mul_card_range ψ
    rw [hW2, ← hkr]
    calc 2 * (Nat.card ψ.ker * Nat.card ψ.range) = 2 * Nat.card ψ.range * Nat.card ψ.ker := by ring
      _ ≤ 2 * Nat.card ψ.range * _ := Nat.mul_le_mul_left _ hker

end CFSG.Quasithin.Background.Harris.R1
