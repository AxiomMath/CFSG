module

public import CFSG.Quasithin.Background.A1cA131Reduced
public import CFSG.Quasithin.Background.A1cKlein
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace A1c

universe u

variable {p : ℕ} [Fact p.Prime]

theorem exists_action_on_frattini_quotient (hp2 : p ≠ 2) {G : Type u} [Group G] [Finite G]
    (hrk : pRank p (⊤ : Subgroup G) ≤ 2) {P : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    (hP1 : P ≠ ⊥) (hC : Subgroup.centralizer (P : Set G) ≤ P) :
    ∃ (W : Type u) (_ : Group W) (_ : Finite W) (θ : G →* MulAut W),
      (∀ a b : W, a * b = b * a) ∧ (∀ a : W, a ^ p = 1) ∧ Nat.card W ≤ p ^ 2 ∧
        ∀ g ∈ θ.ker, ∃ n : ℕ, g ^ p ^ n = 1 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hP1
  obtain ⟨D, hDc, -, hDexp, -, -, hDker⟩ :=
    CFSG.SectionRank.Ccomm.supercritical_witness hp2 hP
  have hDp : IsPGroup p ↥D := hP.to_subgroup D
  obtain ⟨hchar, hWcomm, hWpow⟩ := CFSG.SectionRank.Ccomm.frattini_quotient_elementary hDp
  have hexp : ∀ x : ↥D, x ^ p = 1 := fun x => Subtype.ext (hDexp x.1 x.2)
  have hrkD : pRank p (⊤ : Subgroup ↥D) ≤ 2 := by
    refine le_trans (CFSG.SectionRank.pRank_top_le_of_injective hp1 (P.subtype.comp D.subtype)
      ?_) hrk
    exact Subtype.val_injective.comp Subtype.val_injective
  have hcard := (CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound hDp hexp hrkD).2
  refine ⟨↥D ⧸ frattini ↥D, inferInstance, inferInstance,
    (CFSG.SectionRank.Ccomm.frattiniAction D).comp (MulAut.conjNormal : G →* MulAut ↥P),
    hWcomm, hWpow, hcard, ?_⟩
  intro g hg
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
  have hg' : (MulAut.conjNormal g : MulAut ↥P) ∈ (CFSG.SectionRank.Ccomm.frattiniAction D).ker :=
    hg
  obtain ⟨m, hm⟩ := hDker ⟨_, hg'⟩
  have hm' : (MulAut.conjNormal g : MulAut ↥P) ^ p ^ m = 1 := congrArg Subtype.val hm
  have hgc : g ^ p ^ m ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg (fun α : MulAut ↥P => ((α ⟨y, hy⟩ : ↥P) : G)) (show
      MulAut.conjNormal (g ^ p ^ m) = (1 : MulAut ↥P) by rw [map_pow]; exact hm')
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  obtain ⟨l, hl⟩ := hP ⟨g ^ p ^ m, hC hgc⟩
  refine ⟨m + l, ?_⟩
  have hl' : (g ^ p ^ m) ^ p ^ l = 1 := congrArg Subtype.val hl
  rw [← pow_mul, ← pow_add] at hl'
  exact hl'

section Inverting

variable {Q : Type*} [Group Q]

theorem card_le_of_isCyclic_of_pow {C : Subgroup Q} [IsCyclic C] (hC : ∀ x ∈ C, x ^ p = 1) :
    Nat.card C ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have h1 : Nat.card C = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have h2 : g ^ p = 1 := Subtype.ext (by simpa using hC g.1 g.2)
  rw [h1]
  exact Nat.le_of_dvd (Fact.out : p.Prime).pos (orderOf_dvd_of_pow_eq_one h2)

theorem exists_mul_eq_of_inverting (hp2 : p ≠ 2) {Pb : Subgroup Q} [Pb.Normal]
    (hcomm : ∀ x ∈ Pb, ∀ y ∈ Pb, x * y = y * x) (hexp : ∀ x ∈ Pb, x ^ p = 1) {t s : Q}
    (hs : s * s = 1) (hinv : ∀ x ∈ Pb, t * x * t⁻¹ = x⁻¹) :
    ∀ x ∈ Pb, ∃ y ∈ Pb ⊓ Subgroup.centralizer ({s} : Set Q),
      ∃ v ∈ Pb ⊓ Subgroup.centralizer ({t * s} : Set Q), x = y * v := by
  intro x hx
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  set x' : Q := x ^ (k + 1) with hx'
  have hx'P : x' ∈ Pb := Pb.pow_mem hx _
  have hxx' : x = x' * x' := by
    rw [hx', ← pow_add, show k + 1 + (k + 1) = p + 1 by omega, pow_succ, hexp x hx, one_mul]
  set w : Q := s * x' * s⁻¹ with hw
  have hwP : w ∈ Pb := Subgroup.Normal.conj_mem ‹Pb.Normal› x' hx'P s
  have e1 : s * w * s⁻¹ = x' := by
    calc s * w * s⁻¹ = (s * s) * x' * (s * s)⁻¹ := by rw [hw]; group
      _ = x' := by rw [hs]; simp
  have hyP : x' * w ∈ Pb := Pb.mul_mem hx'P hwP
  have hvP : x' * w⁻¹ ∈ Pb := Pb.mul_mem hx'P (Pb.inv_mem hwP)
  refine ⟨x' * w, ⟨hyP, ?_⟩, x' * w⁻¹, ⟨hvP, ?_⟩, ?_⟩
  · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh]
    have : s * (x' * w) * s⁻¹ = x' * w := by
      calc s * (x' * w) * s⁻¹ = (s * x' * s⁻¹) * (s * w * s⁻¹) := by group
        _ = w * x' := by rw [e1]
        _ = x' * w := hcomm w hwP x' hx'P
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh]
    have e2 : s * w⁻¹ * s⁻¹ = x'⁻¹ := by
      calc s * w⁻¹ * s⁻¹ = (s * w * s⁻¹)⁻¹ := by group
        _ = x'⁻¹ := by rw [e1]
    have e3 : t * w * t⁻¹ = w⁻¹ := hinv w hwP
    have e4 : t * x'⁻¹ * t⁻¹ = x' := by
      calc t * x'⁻¹ * t⁻¹ = (t * x' * t⁻¹)⁻¹ := by group
        _ = x' := by rw [hinv x' hx'P, inv_inv]
    have : (t * s) * (x' * w⁻¹) * (t * s)⁻¹ = x' * w⁻¹ := by
      calc (t * s) * (x' * w⁻¹) * (t * s)⁻¹
          = (t * (s * x' * s⁻¹) * t⁻¹) * (t * (s * w⁻¹ * s⁻¹) * t⁻¹) := by group
        _ = (t * w * t⁻¹) * (t * x'⁻¹ * t⁻¹) := by rw [← hw, e2]
        _ = w⁻¹ * x' := by rw [e3, e4]
        _ = x' * w⁻¹ := hcomm _ (Pb.inv_mem hwP) _ hx'P
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  · rw [hxx']
    calc x' * x' = (x' * w) * (x' * w⁻¹) := by
          calc x' * x' = x' * (w * x') * w⁻¹ := by
                rw [hcomm w hwP x' hx'P]; group
            _ = (x' * w) * (x' * w⁻¹) := by group
      _ = (x' * w) * (x' * w⁻¹) := rfl

end Inverting

theorem exists_klein_pair {Q : Type*} [Group Q] [Finite Q] {T : Subgroup Q}
    (hTcard : Nat.card T = 4) : ∃ a ∈ T, ∃ b ∈ T, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : T)
  have : ∃ b : T, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hle : Nat.card T ≤ 2 := by
      have : Fintype T := Fintype.ofFinite T
      rw [Nat.card_eq_fintype_card]
      calc Fintype.card T = (Finset.univ : Finset T).card := Finset.card_univ.symm
        _ ≤ ({1, a} : Finset T).card := Finset.card_le_card (fun b _ => by
            by_cases hb : b = 1
            · simp [hb]
            · simp [h b hb])
        _ ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨b, hb1, hba⟩ := this
  exact ⟨a, a.2, b, b.2, fun h => ha (Subtype.ext h), fun h => hb1 (Subtype.ext h),
    fun h => hba (Subtype.ext h.symm)⟩

theorem card_le_mul_of_forall_mul {Q : Type*} [Group Q] [Finite Q] {Pb C₁ C₂ : Subgroup Q}
    (h₁ : C₁ ≤ Pb) (h₂ : C₂ ≤ Pb) (h : ∀ x ∈ Pb, ∃ y ∈ C₁, ∃ v ∈ C₂, x = y * v) :
    Nat.card Pb ≤ Nat.card C₁ * Nat.card C₂ := by
  let f : ↥C₁ × ↥C₂ → ↥Pb := fun z => ⟨z.1 * z.2, Pb.mul_mem (h₁ z.1.2) (h₂ z.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, v, hv, rfl⟩ := h x hx
    exact ⟨(⟨y, hy⟩, ⟨v, hv⟩), rfl⟩
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_surjective f hf

theorem isPGroup_two_zpowers {Q : Type*} [Group Q] {x : Q} (hx : x ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem centralizer_singleton_le_zpowers {Q : Type*} [Group Q] (x : Q) :
    Subgroup.centralizer ({x} : Set Q) ≤
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup Q) : Set Q) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro g hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  have : x * y = y * x := hy x (Set.mem_singleton x)
  exact ((Commute.zpow_left (show Commute x y from this) k).eq)

theorem reduced_exists_invariant_subgroup (hp2 : p ≠ 2) {G : Type u} [Group G] [Finite G]
    {Q : Type*} [Group Q] [Finite Q] {φ : G →* Q} (hφ : Function.Surjective φ)
    (hker : IsPGroup p φ.ker) (hrk : pRank p (⊤ : Subgroup G) ≤ 2)
    (hF : Subgroup.centralizer (pCore p Q : Set Q) ≤ pCore p Q)
    (hel : IsElemAbelian p (pCore p Q)) (hcard : Nat.card (pCore p Q) = p ^ 3)
    (h2 : 1 < pRank 2 (⊤ : Subgroup Q)) :
    ∃ W : Subgroup Q, W ≤ pCore p Q ∧ W.Normal ∧ W ≠ ⊥ ∧ W ≠ pCore p Q := by
  by_contra hcon
  push Not at hcon
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPbn : (pCore p Q).Normal := CFSG.pCore_normal (G := Q) (p := p)
  have hPn := preCore_normal (p := p) φ
  have hPp := isPGroup_preCore hker
  have hC := centralizer_preCore_le hφ hF
  have hPbcomm : ∀ x ∈ pCore p Q, ∀ y ∈ pCore p Q, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hP1 : preCore p φ ≠ ⊥ := by
    intro h
    have hb : pCore p Q = ⊥ := by rw [← map_preCore hφ, h, Subgroup.map_bot]
    rw [hb, Subgroup.card_bot] at hcard
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp1
    omega
  obtain ⟨W, _, _, θ, hWcomm, hWpow, hWcard, hθker⟩ :=
    exists_action_on_frattini_quotient hp2 hrk hPp hP1 hC
  have hkerP : θ.ker ≤ preCore p φ := by
    intro g hg
    have hKp : IsPGroup p ↥θ.ker := fun x => by
      obtain ⟨n, hn⟩ := hθker x.1 x.2
      exact ⟨n, Subtype.ext hn⟩
    have hmapp : IsPGroup p ↥(θ.ker.map φ) := hKp.map φ
    have hmn : (θ.ker.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
    have : θ.ker.map φ ≤ pCore p Q := le_pCore p hmn hmapp
    exact this ⟨g, hg, rfl⟩
  have hker2 : ¬ 2 ∣ Nat.card φ.ker := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hker
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)).symm
  have e1 := CFSG.SectionRank.pRank_quotient_eq (p := 2) φ.ker hker2
  have e2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 2) Nat.prime_two.one_lt
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have hrk2 : 2 ≤ pRank 2 (⊤ : Subgroup G) := by rw [← e1, e2]; omega
  obtain ⟨T, hT, hTcard⟩ := exists_isElemAbelian_card_pow Nat.prime_two (n := 2) hrk2
  have hTcard' : Nat.card T = 4 := by rw [hTcard]; norm_num
  obtain ⟨a, haT, b, hbT, ha1, hb1, hab⟩ := exists_klein_pair hTcard'
  have hsq : ∀ x ∈ T, x ^ 2 = 1 := hT.2
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hT.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hθne : ∀ x ∈ T, x ≠ 1 → θ x ≠ 1 := by
    intro x hxT hx1 h
    obtain ⟨n, hn⟩ := hθker x (by rw [MonoidHom.mem_ker]; exact h)
    exact hx1 (eq_one_of_sq_eq_one_of_pow hp2 (hsq x hxT) ⟨n, hn⟩)
  have hmul_ne : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x * y ≠ 1 := by
    intro x hx y hy hxy h
    apply hxy
    have h1 : x = y⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq y hy)
  have habT : a * b ∈ T := T.mul_mem haT hbT
  have hab1 : a * b ≠ 1 := hmul_ne a haT b hbT hab
  obtain ⟨t, s, htT, hsT, ht1, hs1, hst, htW⟩ : ∃ t s : G, t ∈ T ∧ s ∈ T ∧ t ≠ 1 ∧ s ≠ 1 ∧
      s ≠ t ∧ ∀ w : W, θ t w = w⁻¹ := by
    rcases exists_inverting_element hp2 hWcomm hWpow hWcard θ (hsq a haT) (hsq b hbT)
      (hTcomm a haT b hbT) (hθne a haT ha1) (hθne b hbT hb1) (hθne _ habT hab1) with h | h | h
    · exact ⟨a, b, haT, hbT, ha1, hb1, fun e => hab e.symm, h⟩
    · exact ⟨b, a, hbT, haT, hb1, ha1, hab, h⟩
    · refine ⟨a * b, a, habT, haT, hab1, ha1, fun e => hb1 ?_, h⟩
      exact mul_left_cancel (e.symm.trans (mul_one a).symm)
  have ht2 : t ^ 2 = 1 := hsq t htT
  have hs2 : s ^ 2 = 1 := hsq s hsT
  have htt : t * t = 1 := by rw [← sq]; exact ht2
  have hss : s * s = 1 := by rw [← sq]; exact hs2
  have hts : t * s = s * t := hTcomm t htT s hsT
  have hord_t : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have htsT : t * s ∈ T := T.mul_mem htT hsT
  have hts1 : t * s ≠ 1 := hmul_ne t htT s hsT (fun e => hst e.symm)
  have hcommP : ∀ g : G, ⁅t, g⁆ ∈ preCore p φ := by
    intro g
    apply hkerP
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    show θ t * θ g = θ g * θ t
    ext w
    simp only [MulAut.mul_apply, htW, map_inv]
  set tb : Q := φ t with htb
  have hcommPb : ∀ q : Q, ⁅tb, q⁆ ∈ pCore p Q := by
    intro q
    obtain ⟨g, rfl⟩ := hφ q
    have := hcommP g
    rwa [mem_preCore, map_commutatorElement] at this
  have hW0n : (pCore p Q ⊓ Subgroup.centralizer ({tb} : Set Q)).Normal := by
    refine ⟨fun c hc q => ⟨Subgroup.Normal.conj_mem hPbn c hc.1 q, ?_⟩⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh]
    have hz : tb * q⁻¹ * tb⁻¹ * q ∈ pCore p Q := by
      have := hcommPb q⁻¹
      rwa [commutatorElement_def, inv_inv] at this
    have hct : tb * c = c * tb :=
      Subgroup.mem_centralizer_iff.1 hc.2 tb (Set.mem_singleton _)
    have hcz : c * (tb * q⁻¹ * tb⁻¹ * q)⁻¹ = (tb * q⁻¹ * tb⁻¹ * q)⁻¹ * c :=
      hPbcomm c hc.1 _ ((pCore p Q).inv_mem hz)
    have hy : c * (q⁻¹ * tb * q) = (q⁻¹ * tb * q) * c := by
      have e : q⁻¹ * tb * q = (tb * q⁻¹ * tb⁻¹ * q)⁻¹ * tb := by group
      rw [e]
      calc c * ((tb * q⁻¹ * tb⁻¹ * q)⁻¹ * tb) = (c * (tb * q⁻¹ * tb⁻¹ * q)⁻¹) * tb :=
            (mul_assoc _ _ _).symm
        _ = (tb * q⁻¹ * tb⁻¹ * q)⁻¹ * (c * tb) := by rw [hcz, mul_assoc]
        _ = (tb * q⁻¹ * tb⁻¹ * q)⁻¹ * (tb * c) := by rw [hct]
        _ = ((tb * q⁻¹ * tb⁻¹ * q)⁻¹ * tb) * c := (mul_assoc _ _ _).symm
    calc tb * (q * c * q⁻¹) = q * ((q⁻¹ * tb * q) * c) * q⁻¹ := by group
      _ = q * (c * (q⁻¹ * tb * q)) * q⁻¹ := by rw [hy]
      _ = q * c * q⁻¹ * tb := by group
  by_cases hW0 : pCore p Q ⊓ Subgroup.centralizer ({tb} : Set Q) = ⊥
  · exfalso
    have htb2 : tb ^ 2 = 1 := by rw [htb, ← map_pow, ht2, map_one]
    have htbtb : tb * tb = 1 := by rw [← sq]; exact htb2
    have hinv : ∀ x ∈ pCore p Q, tb * x * tb⁻¹ = x⁻¹ := by
      intro x hx
      have hxP : tb * x * tb⁻¹ ∈ pCore p Q := Subgroup.Normal.conj_mem hPbn x hx tb
      have hu : x * (tb * x * tb⁻¹) ∈ pCore p Q ⊓ Subgroup.centralizer ({tb} : Set Q) := by
        refine ⟨(pCore p Q).mul_mem hx hxP, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
        rw [Set.mem_singleton_iff.1 hh]
        have e : tb * (x * (tb * x * tb⁻¹)) * tb⁻¹ = x * (tb * x * tb⁻¹) := by
          calc tb * (x * (tb * x * tb⁻¹)) * tb⁻¹
              = (tb * x * tb⁻¹) * (tb * tb * x * (tb * tb)⁻¹) := by group
            _ = (tb * x * tb⁻¹) * x := by rw [htbtb]; simp
            _ = x * (tb * x * tb⁻¹) := hPbcomm _ hxP _ hx
        rw [mul_inv_eq_iff_eq_mul] at e
        exact e
      rw [hW0, Subgroup.mem_bot] at hu
      exact eq_inv_of_mul_eq_one_right hu
    have hnotker : ∀ x : G, x ^ 2 = 1 → x ≠ 1 → φ x ≠ 1 := by
      intro x hx2 hx1 h
      obtain ⟨n, hn⟩ := hker ⟨x, by rw [MonoidHom.mem_ker]; exact h⟩
      exact hx1 (eq_one_of_sq_eq_one_of_pow hp2 hx2 ⟨n, congrArg Subtype.val hn⟩)
    set sb : Q := φ s with hsb
    have hsb2 : sb * sb = 1 := by rw [hsb, ← map_mul, hss, map_one]
    have hsb1 : sb ≠ 1 := hnotker s hs2 hs1
    have htsb : tb * sb = sb * tb := by rw [htb, hsb, ← map_mul, ← map_mul, hts]
    have hts2 : (t * s) ^ 2 = 1 := hsq (t * s) htsT
    have htsb1 : tb * sb ≠ 1 := by
      have := hnotker (t * s) hts2 hts1
      rwa [map_mul] at this
    have htsb2 : (tb * sb) ^ 2 = 1 := by rw [htb, hsb, ← map_mul, ← map_pow, hts2, map_one]
    have hcyc₁ : IsCyclic ↥(pCore p Q ⊓ Subgroup.centralizer (Subgroup.zpowers sb : Set Q)) :=
      reduced_isCyclic_centralizer hp2 hφ hker hrk hF
        (isPGroup_two_zpowers (by rw [pow_two]; exact hsb2))
        (fun h => hsb1 (by
          have : sb ∈ Subgroup.zpowers sb := Subgroup.mem_zpowers sb
          rw [h] at this; exact Subgroup.mem_bot.1 this))
    have hcyc₂ : IsCyclic ↥(pCore p Q ⊓
        Subgroup.centralizer (Subgroup.zpowers (tb * sb) : Set Q)) :=
      reduced_isCyclic_centralizer hp2 hφ hker hrk hF (isPGroup_two_zpowers htsb2)
        (fun h => htsb1 (by
          have : tb * sb ∈ Subgroup.zpowers (tb * sb) := Subgroup.mem_zpowers _
          rw [h] at this; exact Subgroup.mem_bot.1 this))
    have hc₁ : IsCyclic ↥(pCore p Q ⊓ Subgroup.centralizer ({sb} : Set Q)) :=
      Subgroup.isCyclic_of_le (inf_le_inf_left _ (centralizer_singleton_le_zpowers sb))
    have hc₂ : IsCyclic ↥(pCore p Q ⊓ Subgroup.centralizer ({tb * sb} : Set Q)) :=
      Subgroup.isCyclic_of_le (inf_le_inf_left _ (centralizer_singleton_le_zpowers (tb * sb)))
    have hle₁ := card_le_of_isCyclic_of_pow (p := p) (C := pCore p Q ⊓ Subgroup.centralizer
      ({sb} : Set Q)) (fun x hx => hel.2 x hx.1)
    have hle₂ := card_le_of_isCyclic_of_pow (p := p) (C := pCore p Q ⊓ Subgroup.centralizer
      ({tb * sb} : Set Q)) (fun x hx => hel.2 x hx.1)
    have hdec := exists_mul_eq_of_inverting hp2 hPbcomm hel.2 hsb2 hinv
    have hcardle := card_le_mul_of_forall_mul (inf_le_left :
      pCore p Q ⊓ Subgroup.centralizer ({sb} : Set Q) ≤ pCore p Q) (inf_le_left :
      pCore p Q ⊓ Subgroup.centralizer ({tb * sb} : Set Q) ≤ pCore p Q) hdec
    rw [hcard] at hcardle
    have hlt : p * p < p ^ 3 := by
      have hpp : 0 < p * p := Nat.mul_pos (by omega) (by omega)
      calc p * p = p * p * 1 := (mul_one _).symm
        _ < p * p * p := Nat.mul_lt_mul_of_pos_left hp1 hpp
        _ = p ^ 3 := by ring
    have := Nat.mul_le_mul hle₁ hle₂
    omega
  · have hW0Pb := hcon _ inf_le_left hW0n hW0
    have htb_mem : tb ∈ pCore p Q := by
      apply hF
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      have : y ∈ pCore p Q ⊓ Subgroup.centralizer ({tb} : Set Q) := by rw [hW0Pb]; exact hy
      exact (Subgroup.mem_centralizer_iff.1 this.2 tb (Set.mem_singleton _)).symm
    exact not_mem_of_orderOf_eq_two hPp hp2 hord_t htb_mem

end A1c



end CFSG.Quasithin
