module

public import CFSG.RankThree.PartTwo.Sec19.Step1913
public import CFSG.RankThree.PartTwo.KFacts.KS18A7M22
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18

theorem rank3II_19_13_omega_of (hK : KFacts.KS18A7M22) : Step1913Omega := by
  intro G _ _ A c L hD hS hch hL P hP hAP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hL3, hZ, hinn, hexp, hab⟩ := hK _ hL
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hA : CFSG.Assembly.IsElemAbelian 3 A := hD.mem_partTwoF.1
  have hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A :=
    hD.mem_partTwoF.2.1
  have hc := hD.zpowers_mem_omegaA
  have hcA : c ∈ A := hc.1 (Subgroup.mem_zpowers c)
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hc.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := hD.mem_thetaComponentsAt
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hPC : P ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec12.le_centralizer_of_isPGroup hc3 hP3 hP.le
  have huniq := (hch.2 c hc L hD.mem_lA).2
  have hLcard : 3 ∣ Nat.card L := hL3.trans (Subgroup.card_quotient_dvd_card _)
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmem := map_mem_thetaComponentsAt (MulAut.conj h) hLc
    have hhc : h * c * h⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp hh c).mp (Subgroup.mem_zpowers c)
    have hzp : Subgroup.zpowers (h * c * h⁻¹) = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hhc) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers]
      exact ((MulAut.conj h).orderOf_eq c).ge
    have hθeq : thetaComponentsAt 3 (h * c * h⁻¹) = thetaComponentsAt 3 c := by
      rw [thetaComponentsAt_eq_thetaComponentsIn, thetaComponentsAt_eq_thetaComponentsIn,
        centralizer_singleton_eq_of_zpowers_eq hzp]
    have hmem' : L.map (MulAut.conj h).toMonoidHom ∈ thetaComponentsAt 3 c := by
      rw [← hθeq]
      exact hmem
    exact huniq _ hmem'
      (by rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]; exact hLcard)
  have hLH : L ≤ H := le_normalizer_zpowers_of_mem hLc
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := hP.le.trans hHL
  set θL := aschbacherSolvableCore 3 L with hθL
  have hθ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hPθ : ∀ x : L, (x : G) ∈ P → x ∈ θL → x = 1 := by
    intro x hxP hxθ
    obtain ⟨k, hk⟩ := hP3 ⟨x, hxP⟩
    have h1 : x ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card θL := by
      have := orderOf_dvd_natCard (⟨x, hxθ⟩ : θL)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (3 ^ k) (Nat.card θL) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ.2.2.1)
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) h2)
  set ρ : Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ θL) :=
    (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hρ
  have hρmk : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)) (y : L),
      ρ ⟨x, hx⟩ (y : L ⧸ θL) = ((L.normalizerMonoidHom ⟨x, hx⟩ y : L) : L ⧸ θL) :=
    fun x hx y => rfl
  have hnm : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)) (y : L),
      ((L.normalizerMonoidHom ⟨x, hx⟩ y : L) : G) = x * y * x⁻¹ :=
    fun x hx y => Sec4.normalizerMonoidHom_apply_coe hx y
  have hρL : ∀ (l : L) (hl : (l : G) ∈ Subgroup.normalizer (L : Set G)),
      ρ ⟨l, hl⟩ = MulAut.conj (l : L ⧸ θL) := by
    intro l hl
    ext z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    rw [hρmk, MulAut.conj_apply]
    have : (L.normalizerMonoidHom ⟨(l : G), hl⟩ y : L) = l * y * l⁻¹ :=
      Subtype.ext (by rw [hnm]; simp)
    rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hρinner : ∀ (x : G) (hx : x ∈ P), ∃ s : L ⧸ θL, ρ ⟨x, hPN hx⟩ = MulAut.conj s := by
    intro x hx
    obtain ⟨k, hk⟩ := hP3 ⟨x, hx⟩
    have h1 : (⟨x, hPN hx⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    exact hinn _ ⟨k, by rw [← map_pow, h1, map_one]⟩
  set ρP : Subgroup (MulAut (L ⧸ θL)) :=
    (P.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ with hρP
  have hρP3 : IsPGroup 3 ρP := (hP3.comap_subtype (K := Subgroup.normalizer (L : Set G))).map ρ
  set R : Subgroup (L ⧸ θL) := ρP.comap (MulAut.conj : L ⧸ θL →* MulAut (L ⧸ θL)) with hR
  have hR3 : IsPGroup 3 R := by
    rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := hρP3 ⟨_, hs⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : MulAut.conj (s ^ 3 ^ k) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hk
    have h2 : s ^ 3 ^ k ∈ Subgroup.center (L ⧸ θL) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h3 := congrArg (fun σ : MulAut (L ⧸ θL) => σ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc y * s ^ 3 ^ k = s ^ 3 ^ k * y * (s ^ 3 ^ k)⁻¹ * s ^ 3 ^ k := by rw [h3]
        _ = s ^ 3 ^ k * y := by group
    rw [hZ, Subgroup.mem_bot] at h2
    simpa using h2
  obtain ⟨Q, hQ⟩ := hP.inf_of_le_normalizer hLH hHL
  have hQmem : ∀ l : L, l ∈ Q ↔ (l : G) ∈ P := by
    intro l
    constructor
    · intro hl
      have : (l : G) ∈ P ⊓ L := hQ ▸ Subgroup.mem_map_of_mem L.subtype hl
      exact this.1
    · intro hl
      have : (l : G) ∈ (Q : Subgroup L).map L.subtype := hQ ▸ ⟨hl, l.2⟩
      obtain ⟨l', hl', hll'⟩ := this
      rwa [show l = l' from Subtype.ext hll'.symm]
  set Qb := Q.mapSurjective (QuotientGroup.mk'_surjective θL) with hQb
  have hQbR : (Qb : Subgroup (L ⧸ θL)) ≤ R := by
    rintro _ ⟨l, hl, rfl⟩
    have hlP : (l : G) ∈ P := (hQmem l).mp hl
    change MulAut.conj (QuotientGroup.mk' θL l) ∈ ρP
    rw [QuotientGroup.mk'_apply, ← hρL l (hPN hlP)]
    exact ⟨⟨(l : G), hPN hlP⟩, Subgroup.mem_subgroupOf.mpr hlP, rfl⟩
  have hRQ : R = Qb := Qb.is_maximal' hR3 hQbR
  have hdecomp : ∀ x ∈ P, ∃ l : L, (l : G) ∈ P ∧
      ∀ hy : (l : G)⁻¹ * x ∈ Subgroup.normalizer (L : Set G), ρ ⟨(l : G)⁻¹ * x, hy⟩ = 1 := by
    intro x hx
    obtain ⟨s, hs⟩ := hρinner x hx
    have hsR : s ∈ R := by
      change MulAut.conj s ∈ ρP
      rw [← hs]
      exact ⟨⟨x, hPN hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hRQ] at hsR
    obtain ⟨l, hl, rfl⟩ := hsR
    have hlP : (l : G) ∈ P := (hQmem l).mp hl
    refine ⟨l, hlP, fun hy => ?_⟩
    have h1 : (⟨(l : G)⁻¹ * x, hy⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨(l : G), hPN hlP⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨x, hPN hx⟩ := rfl
    rw [h1, map_mul, map_inv, hs, hρL l (hPN hlP), QuotientGroup.mk'_apply, inv_mul_cancel]
  have hcomm : ∀ l : L, (l : G) ∈ P → ∀ y (hy : y ∈ P), ρ ⟨y, hPN hy⟩ = 1 →
      (l : G) * y = y * l := by
    intro l hlP y hy hρy
    have h1 := congrArg (fun σ : MulAut (L ⧸ θL) => σ (l : L ⧸ θL)) hρy
    simp only [MulAut.one_apply] at h1
    rw [hρmk, QuotientGroup.eq] at h1
    set n := L.normalizerMonoidHom ⟨y, hPN hy⟩ l with hn
    have hnG : (n : G) = y * l * y⁻¹ := hnm y (hPN hy) l
    have h2 : n⁻¹ * l = 1 := by
      refine hPθ _ ?_ h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnG]
      exact P.mul_mem (P.inv_mem (P.mul_mem (P.mul_mem hy hlP) (P.inv_mem hy))) hlP
    have h3 : (n : G) = l := by
      rw [show n = l from inv_mul_eq_one.mp h2]
    rw [hnG] at h3
    calc (l : G) * y = y * l * y⁻¹ * y := by rw [h3]
      _ = y * l := by group
  have hPL3 : ∀ l : L, (l : G) ∈ P → (l : G) ^ 3 = 1 := by
    intro l hlP
    obtain ⟨k, hk⟩ := hP3 ⟨l, hlP⟩
    have hlk : l ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h1 : (l : L ⧸ θL) ^ 3 = 1 := hexp _ ⟨k, by rw [← QuotientGroup.mk_pow, hlk]; rfl⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    have h2 := hPθ _ (by simpa using P.pow_mem hlP 3) h1
    simpa using congrArg Subtype.val h2
  have hPLab : ∀ l₁ l₂ : L, (l₁ : G) ∈ P → (l₂ : G) ∈ P → (l₁ : G) * l₂ = l₂ * l₁ := by
    intro l₁ l₂ h₁ h₂
    have hQab := hab (Qb : Subgroup (L ⧸ θL)) Qb.isPGroup'
    have hm₁ : (l₁ : L ⧸ θL) ∈ (Qb : Subgroup (L ⧸ θL)) := ⟨l₁, (hQmem l₁).mpr h₁, rfl⟩
    have hm₂ : (l₂ : L ⧸ θL) ∈ (Qb : Subgroup (L ⧸ θL)) := ⟨l₂, (hQmem l₂).mpr h₂, rfl⟩
    have h1 := congrArg Subtype.val (hQab.is_comm.comm ⟨_, hm₁⟩ ⟨_, hm₂⟩)
    simp only [Subgroup.coe_mul] at h1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    have h2 := hPθ _ (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact P.mul_mem (P.inv_mem (P.mul_mem h₁ h₂)) (P.mul_mem h₂ h₁)) h1
    have h3 : l₁ * l₂ = l₂ * l₁ := inv_mul_eq_one.mp h2
    exact congrArg Subtype.val h3
  have hcommA : ∀ l : L, (l : G) ∈ P → ∀ a ∈ A, a * l = l * a := by
    intro l hlP a ha
    obtain ⟨l', hl'P, hy⟩ := hdecomp a (hAP ha)
    have hyP : (l' : G)⁻¹ * a ∈ P := P.mul_mem (P.inv_mem hl'P) (hAP ha)
    have h1 := hcomm l hlP _ hyP (hy (hPN hyP))
    have h2 := hPLab l l' hlP hl'P
    calc a * l = (l' : G) * ((l' : G)⁻¹ * a) * l := by group
      _ = (l' : G) * (l * ((l' : G)⁻¹ * a)) := by rw [mul_assoc, ← h1]
      _ = l * ((l' : G) * ((l' : G)⁻¹ * a)) := by rw [← mul_assoc, ← h2, mul_assoc]
      _ = l * a := by group
  have hPLA : ∀ l : L, (l : G) ∈ P → (l : G) ∈ A := by
    intro l hlP
    have hab' := Sec15.isElemAbelian_sup_zpowers hA (hPL3 l hlP) (fun e he => hcommA l hlP e he)
    have heq := hAmax _ hab' le_sup_left
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hAF : ∀ a (ha : a ∈ A), ρ ⟨a, hPN (hAP ha)⟩ = 1 → a ∈ Subgroup.zpowers c := by
    intro a ha hρa
    have hsc : a ∈ sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
      refine ⟨ha, fun x hx => ?_⟩
      have h1 := congrArg (fun σ : MulAut (L ⧸ θL) => σ ((⟨x, hx⟩ : L) : L ⧸ θL)) hρa
      simp only [MulAut.one_apply] at h1
      rw [hρmk] at h1
      set n := L.normalizerMonoidHom ⟨a, hPN (hAP ha)⟩ ⟨x, hx⟩ with hn
      have hnG : (n : G) = a * x * a⁻¹ := hnm a (hPN (hAP ha)) ⟨x, hx⟩
      have h2 : n * (⟨x, hx⟩ : L)⁻¹ ∈ θL := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
          mul_inv_cancel]
      refine ⟨_, h2, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hnG]
    have := hD.mem_lA.2.2.1
    rw [this] at hsc
    exact hsc
  have hAdec : ∀ a ∈ A, ∃ l : L, (l : G) ∈ P ∧ (l : G)⁻¹ * a ∈ Subgroup.zpowers c := by
    intro a ha
    obtain ⟨l, hlP, hy⟩ := hdecomp a (hAP ha)
    have hyA : (l : G)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem (hPLA l hlP)) ha
    exact ⟨l, hlP, hAF _ hyA (hy _)⟩
  have hyA : ∀ y (hy : y ∈ P), ρ ⟨y, hPN hy⟩ = 1 → y ^ 3 = 1 → y ∈ A := by
    intro y hy hρy hy3
    have hyc : ∀ a ∈ A, a * y = y * a := by
      intro a ha
      obtain ⟨l, hlP, hlc⟩ := hAdec a ha
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hlc
      have hca : a = (l : G) * c ^ k := by rw [hk]; group
      have h1 := hcomm l hlP y hy hρy
      have h2 : c ^ k * y = y * c ^ k := by
        have hyc : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp (hPC hy)
        exact ((Commute.zpow_left hyc.symm k).eq)
      rw [hca, mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
    have hab' := Sec15.isElemAbelian_sup_zpowers hA hy3 hyc
    have heq := hAmax _ hab' le_sup_left
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  apply le_antisymm
  · refine (Subgroup.closure_le A).mpr ?_
    rintro x ⟨hxP, hx3⟩
    obtain ⟨l, hlP, hy⟩ := hdecomp x hxP
    have hyP : (l : G)⁻¹ * x ∈ P := P.mul_mem (P.inv_mem hlP) hxP
    have hρy := hy (hPN hyP)
    have hly : (l : G) * ((l : G)⁻¹ * x) = ((l : G)⁻¹ * x) * l := hcomm l hlP _ hyP hρy
    have hy3 : ((l : G)⁻¹ * x) ^ 3 = 1 := by
      have h1 : x = (l : G) * ((l : G)⁻¹ * x) := by group
      have h2 : x ^ 3 = (l : G) ^ 3 * ((l : G)⁻¹ * x) ^ 3 := by
        conv_lhs => rw [h1]
        exact (Commute.mul_pow hly 3)
      rw [hx3, hPL3 l hlP, one_mul] at h2
      exact h2.symm
    have h1 : x = (l : G) * ((l : G)⁻¹ * x) := by group
    rw [h1]
    exact A.mul_mem (hPLA l hlP) (hyA _ hyP hρy hy3)
  · intro a ha
    exact Subgroup.subset_closure ⟨hAP ha, hA.2 a ha⟩

end CFSG.RankThree.PartTwo.Sec19
