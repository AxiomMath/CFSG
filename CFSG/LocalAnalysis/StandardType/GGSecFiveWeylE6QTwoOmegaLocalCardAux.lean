module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInnerQAux
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.LieType.SeitzGeneration.ExcHigh.Generic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open
open CFSG.StandardType.E6QTwo

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

private theorem aux_center_RPlus_eq_bot (hK : Nat.card K = 2) :
    Subgroup.center (OrthRest.RPlus K 4) = ⊥ := by
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  obtain ⟨hbij, hZ⟩ := OrthRest.spinPlus_bij (K := K) (n := 4) (by norm_num)
  let e : ↥(spinGroup (CFSG.LieType.Universal.Spin.quadPlus 4 K)) ≃*
      OrthRest.RPlus K 4 := MulEquiv.ofBijective _ hbij
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := e.surjective z
  have hx : x ∈ Subgroup.center
      (spinGroup (CFSG.LieType.Universal.Spin.quadPlus 4 K)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    apply e.injective
    rw [map_mul, map_mul]
    exact hz (e y)
  rw [hZ, Subgroup.mem_bot] at hx
  rw [hx, map_one]
  exact one_mem _

private theorem aux_exists_innerHom (hK : Nat.card K = 2) {Bs L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (hperf : commutator ↥L = ⊤)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K 4),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ χ : Bs →* OrthRest.RPlus K 4,
      χ.ker = (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs ∧
      ∀ b : Bs, MulAut.conj (χ b) =
        (MulAut.congr θ)
          (e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hBsN b)) := by
  classical
  let action := e6QTwoBstarConjAction hBsN
  let β : Bs →* MulAut (OrthRest.RPlus K 4) :=
    (MulAut.congr θ).toMonoidHom.comp ((e6QTwoQuotCenterAutHom L).comp action)
  have hβ_apply : ∀ (b : Bs) (l : ↥L),
      β b (θ (QuotientGroup.mk' (Subgroup.center L) l)) =
        θ (QuotientGroup.mk' (Subgroup.center L) (action b l)) := by
    intro b l
    rw [show β b = (MulAut.congr θ) (e6QTwoQuotCenterAutHom L (action b)) from rfl,
      e6QTwoMulAutCongrApply, e6QTwoQuotCenterAutHom_mk]
  have hβ_inner : ∀ b : Bs,
      β b ∈ (MulAut.conj : OrthRest.RPlus K 4 →* MulAut _).range := by
    intro b
    obtain ⟨φ, ⟨t, rfl⟩, hφ⟩ := hI ((b : G)⁻¹) (inv_mem b.2)
    refine ⟨t, ?_⟩
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
    rw [hβ_apply b l]
    simp only [QuotientGroup.mk'_apply]
    exact hφ l (action b l) (by
      simpa using e6QTwoBstarConjAction_apply hBsN b l)
  let econj := MonoidHom.ofInjective
    (OrthRest.conj_injective (aux_center_RPlus_eq_bot hK) :
      Function.Injective
        (MulAut.conj : OrthRest.RPlus K 4 →* MulAut (OrthRest.RPlus K 4)))
  let χ : Bs →* OrthRest.RPlus K 4 :=
    econj.symm.toMonoidHom.comp (β.codRestrict _ hβ_inner)
  have hχconj : ∀ b : Bs, MulAut.conj (χ b) = β b := by
    intro b
    have h1 : econj (χ b) = β.codRestrict _ hβ_inner b := by
      simp [χ]
    simpa [econj, MonoidHom.ofInjective_apply] using congrArg Subtype.val h1
  have hβker : β.ker = (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hb
      have hβb : (MulAut.congr θ)
          (e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hBsN b)) = 1 := hb
      have hφ1 : e6QTwoQuotCenterAutHom L (e6QTwoBstarConjAction hBsN b) = 1 :=
        (MulAut.congr θ).injective (by
          rw [hβb]; exact (map_one (MulAut.congr θ)).symm)
      have h2 : e6QTwoBstarConjAction hBsN b = 1 :=
        e6QTwoQuotCenterAutHom_injective hperf (by rw [hφ1, map_one])
      exact ⟨b.2, (e6QTwoBstarConjAction_eq_one_iff hBsN b).mp h2⟩
    · rintro ⟨-, hbC⟩
      have h1 : e6QTwoBstarConjAction hBsN b = 1 :=
        (e6QTwoBstarConjAction_eq_one_iff hBsN b).mpr hbC
      rw [show β b = (MulAut.congr θ) (e6QTwoQuotCenterAutHom L
        (e6QTwoBstarConjAction hBsN b)) from rfl, h1, map_one, map_one]
  refine ⟨χ, ?_, hχconj⟩
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have h1 : χ b = 1 ↔ β b = 1 := by
    constructor
    · intro hb
      rw [← hχconj b, hb, map_one]
    · intro hb
      apply (OrthRest.conj_injective (aux_center_RPlus_eq_bot hK))
      rw [hχconj b, hb, map_one]
  rw [h1, ← Subgroup.mem_subgroupOf, ← hβker, MonoidHom.mem_ker]

theorem E6QTwo.card_le_three_pow_five_of_omegaPlus (hK : Nat.card K = 2)
    {Bs L : Subgroup G} {x : G} (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K 4),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    Nat.card Bs ≤ 3 ^ 5 := by
  classical
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  obtain ⟨χ, hχker, -⟩ := aux_exists_innerHom hK θ hperf hBsN hI
  have hχea : IsElemAbelian 3 χ.range := by
    have htop : IsElemAbelian 3 (⊤ : Subgroup ↥Bs) := by
      simpa using hBs.subgroupOf Bs
    have := htop.map χ
    simpa [MonoidHom.range_eq_map] using this
  have hχcard : Nat.card χ.range ≤ 3 ^ 4 := by
    have h := OrthRest.card_le_plus (m := 4) (by norm_num) Nat.prime_three
      (by norm_num) χ.range hχea
    simpa using h
  have hkercard : Nat.card χ.ker ≤ 3 := by
    rw [hχker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : Bs ⊓ Subgroup.centralizer (L : Set G) ≤ Bs)).toEquiv, hBL,
      Nat.card_zpowers]
    have hxBs : x ∈ Bs := by
      have hx : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
        rw [hBL]; exact Subgroup.mem_zpowers x
      exact (Subgroup.mem_inf.mp hx).1
    have hx3 : x ^ 3 = 1 := hBs.2 x hxBs
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx3)
  have hmul := Subgroup.card_ker_mul_card_range χ
  calc Nat.card Bs = Nat.card χ.ker * Nat.card χ.range := hmul.symm
    _ ≤ 3 * 3 ^ 4 := Nat.mul_le_mul hkercard hχcard
    _ = 3 ^ 5 := by norm_num

theorem E6QTwo.card_inf_eq_of_omegaPlus (hK : Nat.card K = 2)
    {Bs L : Subgroup G} {x : G} (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K 4)
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center L))
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K 4),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ 4 := by
  classical
  haveI : CharP K 2 :=
    CFSG.TauCetiBridge.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK]; rfl)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨χ, hχker, hχconj⟩ := aux_exists_innerHom hK θ hperf hBsN hI
  have hxBL : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hBL]; exact Subgroup.mem_zpowers x
  have hxBs : x ∈ Bs := (Subgroup.mem_inf.mp hxBL).1
  have hx3 : x ^ 3 = 1 := hBs.2 x hxBs
  have hχker3 : Nat.card χ.ker = 3 := by
    rw [hχker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : Bs ⊓ Subgroup.centralizer (L : Set G) ≤ Bs)).toEquiv, hBL,
      Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hχrange3 : Nat.card χ.range = 3 ^ 4 := by
    have hmul := Subgroup.card_ker_mul_card_range χ
    rw [hχker3, hcard] at hmul
    norm_num at hmul ⊢
    omega
  have hχea : IsElemAbelian 3 χ.range := by
    have htop : IsElemAbelian 3 (⊤ : Subgroup ↥Bs) := by
      simpa using hBs.subgroupOf Bs
    have := htop.map χ
    simpa [MonoidHom.range_eq_map] using this
  let π : ↥L →* OrthRest.RPlus K 4 :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = Subgroup.center ↥L := by
    ext y
    rw [MonoidHom.mem_ker]
    show θ (y : ↥L ⧸ Subgroup.center ↥L) = 1 ↔ y ∈ Subgroup.center ↥L
    constructor
    · intro hy
      exact (QuotientGroup.eq_one_iff y).mp (θ.injective (by rw [hy, map_one]))
    · intro hy
      have h1 : (y : ↥L ⧸ Subgroup.center ↥L) = 1 :=
        (QuotientGroup.eq_one_iff y).mpr hy
      rw [h1, map_one]
  have hcop : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπker]
    intro h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
    rw [hk] at h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num : ¬ 3 ∣ 2)
  obtain ⟨E, hEmap, hEdisj, hEea⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.exists_lift_elemAbelian_of_coprime_ker
      (p := 3) π hπ hcop hχea
  have hEcard : Nat.card ↥E = 3 ^ 4 := by
    have h1 : Nat.card ↥(E.map π) = Nat.card ↥E :=
      CFSG.card_map_eq_card_of_inf_ker_eq_bot π (disjoint_iff.mp hEdisj)
    rw [← h1, hEmap, hχrange3]
  have hEs : E.map L.subtype ≤ Bs ⊓ L := by
    rintro _ ⟨e, he, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, e.2⟩
    have heCent : (e : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hbχ : χ ⟨b, hb⟩ ∈ E.map π := by
        rw [hEmap]; exact ⟨⟨b, hb⟩, rfl⟩
      obtain ⟨k, hkE, hkπ⟩ := Subgroup.mem_map.mp hbχ
      have hact : e6QTwoBstarConjAction hBsN ⟨b, hb⟩ = MulAut.conj k := by
        apply e6QTwoQuotCenterAutHom_injective hperf
        apply (MulAut.congr θ).injective
        rw [← hχconj ⟨b, hb⟩, e6QTwoQuotCenterAutHom_conj,
          ← e6QTwoMulAutConjCongr θ (QuotientGroup.mk' (Subgroup.center L) k)]
        exact congrArg MulAut.conj hkπ.symm
      have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBsN hb
      have hkN : (k : G) ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.le_normalizer (H := L) (x := (k : G)) k.2
      let gN : Subgroup.normalizer (L : Set G) :=
        ⟨b, hbN⟩ * (⟨(k : G), hkN⟩)⁻¹
      have hgNcoe : (gN : G) = b * (k : G)⁻¹ := rfl
      have hA : Subgroup.normalizerMonoidHom (H := L) gN = 1 := by
        show Subgroup.normalizerMonoidHom (H := L)
          (⟨b, hbN⟩ * (⟨(k : G), hkN⟩)⁻¹ :
            Subgroup.normalizer (L : Set G)) = 1
        rw [map_mul, map_inv]
        have h1 : Subgroup.normalizerMonoidHom (H := L) ⟨b, hbN⟩ =
            e6QTwoBstarConjAction hBsN ⟨b, hb⟩ := by
          ext l
          rw [e6QTwoBstarConjAction_apply hBsN ⟨b, hb⟩ l]
          exact Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨b, hbN⟩ l
        have h2 : Subgroup.normalizerMonoidHom (H := L) ⟨(k : G), hkN⟩ =
            MulAut.conj k := by
          ext l
          rw [MulAut.conj_apply]
          exact Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨(k : G), hkN⟩ l
        rw [h1, h2, hact, mul_inv_cancel]
      have hcC : b * (k : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
        have hgker : gN ∈ (Subgroup.normalizerMonoidHom (H := L)).ker := by
          rw [MonoidHom.mem_ker]; exact hA
        rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hgker
        simpa [hgNcoe] using hgker
      have hek : (e : G) * (k : G) = (k : G) * (e : G) := by
        have h1 : (⟨e, he⟩ : E) * ⟨k, hkE⟩ = ⟨k, hkE⟩ * ⟨e, he⟩ :=
          hEea.1.is_comm.comm _ _
        exact congrArg (fun z : ↥L => (z : G)) (congrArg Subtype.val h1)
      have hec : (e : G) * (b * (k : G)⁻¹) =
          (b * (k : G)⁻¹) * (e : G) :=
        Subgroup.mem_centralizer_iff.mp hcC (e : G) e.2
      have hmain : (e : G) * b = b * (e : G) := by
        calc (e : G) * b = (e : G) * ((b * (k : G)⁻¹) * (k : G)) := by
              rw [show (b * (k : G)⁻¹) * (k : G) = b by group]
          _ = ((e : G) * (b * (k : G)⁻¹)) * (k : G) := by group
          _ = ((b * (k : G)⁻¹) * (e : G)) * (k : G) := by rw [hec]
          _ = (b * (k : G)⁻¹) * ((e : G) * (k : G)) := by group
          _ = (b * (k : G)⁻¹) * ((k : G) * (e : G)) := by rw [hek]
          _ = ((b * (k : G)⁻¹) * (k : G)) * (e : G) := by group
          _ = b * (e : G) := by
              rw [show (b * (k : G)⁻¹) * (k : G) = b by group]
      exact hmain.symm
    have he3 : (e : G) ^ 3 = 1 := congrArg Subtype.val (hEea.2 e he)
    exact hstar (e : G) heCent he3
  have hlower : 3 ^ 4 ≤ Nat.card ↥(Bs ⊓ L) := by
    have hcardmap : Nat.card ↥(E.map L.subtype) = Nat.card ↥E :=
      Subgroup.card_map_of_injective L.subtype_injective
    calc 3 ^ 4 = Nat.card ↥E := hEcard.symm
      _ = Nat.card ↥(E.map L.subtype) := hcardmap.symm
      _ ≤ Nat.card ↥(Bs ⊓ L) := Subgroup.card_le_of_le hEs
  have hupper : Nat.card ↥(Bs ⊓ L) ≤ 3 ^ 4 := by
    have hzx_le : Subgroup.zpowers x ≤ Bs := by
      rw [← hBL]; exact inf_le_left
    have hdisj : (Bs ⊓ L) ⊓ Subgroup.zpowers x = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      obtain ⟨hyBL, hyx⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨hyBs, hyL⟩ := Subgroup.mem_inf.mp hyBL
      have hyC : y ∈ Subgroup.centralizer (L : Set G) := by
        have hle : Subgroup.zpowers x ≤ Subgroup.centralizer (L : Set G) := by
          rw [← hBL]; exact inf_le_right
        exact hle hyx
      have hyZ : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hyC (l : G) l.2
      have hy3 : y ^ 3 = 1 := hBs.2 y hyBs
      obtain ⟨k, hk⟩ := hZ2 (⟨⟨y, hyL⟩, hyZ⟩ : Subgroup.center ↥L)
      have hy2 : y ^ 2 ^ k = 1 := by
        have h' := congrArg (fun z : Subgroup.center ↥L => ((z : ↥L) : G)) hk
        simpa using h'
      exact e6QTwoEqOneOfPowThreeOfPowTwo hy3 hy2
    let f : ↥(Bs ⊓ L) × ↥(Subgroup.zpowers x) → ↥Bs := fun p =>
      ⟨p.1.1 * p.2.1, Bs.mul_mem p.1.2.1 (hzx_le p.2.2)⟩
    have hf_inj : Function.Injective f := by
      rintro ⟨⟨a, ha⟩, ⟨y, hy⟩⟩ ⟨⟨a', ha'⟩, ⟨y', hy'⟩⟩ hf
      simp only [f, Subtype.mk.injEq] at hf
      have h1 : y * y'⁻¹ = a⁻¹ * a' := by
        calc y * y'⁻¹ = a⁻¹ * (a * y) * y'⁻¹ := by group
          _ = a⁻¹ * (a' * y') * y'⁻¹ := by rw [hf]
          _ = a⁻¹ * a' := by group
      have h2 : a⁻¹ * a' ∈ Bs ⊓ L :=
        ⟨Bs.mul_mem (Bs.inv_mem ha.1) ha'.1, L.mul_mem (L.inv_mem ha.2) ha'.2⟩
      have h3 : y * y'⁻¹ ∈ Subgroup.zpowers x :=
        Subgroup.mul_mem (H := Subgroup.zpowers x) hy
          (Subgroup.inv_mem (H := Subgroup.zpowers x) hy')
      have h4 : a⁻¹ * a' = 1 := by
        have h4' : a⁻¹ * a' ∈ (Bs ⊓ L) ⊓ Subgroup.zpowers x := ⟨h2, h1 ▸ h3⟩
        rwa [hdisj, Subgroup.mem_bot] at h4'
      have haeq : a = a' := by
        have h : a' = a := by
          calc a' = a * (a⁻¹ * a') := by group
            _ = a := by rw [h4, mul_one]
        exact h.symm
      have hyeq : y = y' := by
        have h5 : y * y'⁻¹ = 1 := by rw [h1, h4]
        calc y = (y * y'⁻¹) * y' := by group
          _ = y' := by rw [h5, one_mul]
      exact Prod.ext (Subtype.ext haeq) (Subtype.ext hyeq)
    have hle := Nat.card_le_card_of_injective f hf_inj
    rw [Nat.card_prod, Nat.card_zpowers, orderOf_eq_prime hx3 hx1, hcard] at hle
    norm_num at hle ⊢
    omega
  exact le_antisymm hupper hlower

end CFSG.StandardType

end
