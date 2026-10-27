module

public import CFSG.Quasithin.H13.L32A720c
public import CFSG.Quasithin.H13.L32A719a
public import CFSG.Quasithin.H13.L32A720b
public import CFSG.Quasithin.H13.L32AS4d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.S153Q CFSG.Quasithin.S153Q.Q4A
open scoped commutatorElement

section ChiefGen

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_pre_of_act {X Y A : Subgroup G} (h : IsElemSection X Y)
    {hAX : A ≤ Subgroup.normalizer (X : Set G)} {hAY : A ≤ Subgroup.normalizer (Y : Set G)}
    {W : Subgroup (SecW X Y h)} (hW : ∀ a : ↥A, ∀ w ∈ W, SecW.act h A hAX hAY a w ∈ W) :
    A ≤ Subgroup.normalizer (SecW.pre h W : Set G) := by
  intro a ha
  refine mem_normalizer_of_forall_conj (Q := A) (fun a' ha' x hx => ?_) ha
  obtain ⟨hxX, hxW⟩ := (SecW.mem_pre h).mp hx
  have hx' : a' * x * a'⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hAX ha') x).mp hxX
  refine (SecW.mem_pre h).mpr ⟨hx', ?_⟩
  have := hW ⟨a', ha'⟩ _ hxW
  rw [SecW.act_mk] at this
  exact this

theorem act_eq_one_of_chief {H₀ X Y : Subgroup G} (h : IsElemSection X Y) (hXY : Y < X)
    (hXn : H₀ ≤ Subgroup.normalizer (X : Set G)) (hYn : H₀ ≤ Subgroup.normalizer (Y : Set G))
    (hchief : ∀ X' : Subgroup G, Y ≤ X' → X' ≤ X → H₀ ≤ Subgroup.normalizer (X' : Set G) →
      X' = Y ∨ X' = X)
    {q : G} (hq : q ∈ pCoreOf 2 H₀) :
    SecW.act h H₀ hXn hYn ⟨q, pCoreOf_le 2 _ hq⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := SecW.act h H₀ hXn hYn with hρ
  let F : Subgroup (SecW X Y h) :=
    ⨅ q' : ↥(pCoreOf 2 H₀), fixSub (ρ ⟨q', pCoreOf_le 2 _ q'.2⟩)
  have hmemF : ∀ w, w ∈ F ↔ ∀ q' : ↥(pCoreOf 2 H₀), ρ ⟨q', pCoreOf_le 2 _ q'.2⟩ w = w := by
    intro w
    simp only [F, Subgroup.mem_iInf, mem_fixSub]
  have hFinv : ∀ a : ↥H₀, ∀ w ∈ F, ρ a w ∈ F := by
    intro a w hw
    rw [hmemF] at hw ⊢
    intro q'
    have hq'' : (a : G)⁻¹ * q' * a ∈ pCoreOf 2 H₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H₀ (inv_mem a.2)) q').mp
        q'.2
      simpa using this
    have h1 := hw ⟨_, hq''⟩
    have e : (⟨q', pCoreOf_le 2 _ q'.2⟩ : ↥H₀) * a =
        a * ⟨(a : G)⁻¹ * q' * a, pCoreOf_le 2 _ hq''⟩ := Subtype.ext (by simp [mul_assoc])
    calc ρ ⟨q', pCoreOf_le 2 _ q'.2⟩ (ρ a w) = ρ (⟨q', pCoreOf_le 2 _ q'.2⟩ * a) w := by
          rw [map_mul]
          rfl
      _ = ρ (a * ⟨(a : G)⁻¹ * q' * a, pCoreOf_le 2 _ hq''⟩) w := by rw [e]
      _ = ρ a (ρ ⟨(a : G)⁻¹ * q' * a, pCoreOf_le 2 _ hq''⟩ w) := by
          rw [map_mul]
          rfl
      _ = ρ a w := by rw [h1]
  have hW2 : ∀ w : SecW X Y h, w * w = 1 := SecW.mul_self h
  have hF1 : F ≠ ⊥ := by
    let inst : MulAction ↥(pCoreOf 2 H₀) (SecW X Y h) :=
      { smul := fun q w => ρ (Subgroup.inclusion (pCoreOf_le 2 H₀) q) w
        one_smul := fun w => by
          show ρ (Subgroup.inclusion (pCoreOf_le 2 H₀) 1) w = w
          rw [map_one, map_one, MulAut.one_apply]
        mul_smul := fun q q' w => by
          show ρ (Subgroup.inclusion (pCoreOf_le 2 H₀) (q * q')) w =
            ρ (Subgroup.inclusion (pCoreOf_le 2 H₀) q)
              (ρ (Subgroup.inclusion (pCoreOf_le 2 H₀) q') w)
          rw [map_mul, map_mul, MulAut.mul_apply] }
    have hQ2 : IsPGroup 2 ↥(pCoreOf 2 H₀) := pCoreOf_isPGroup 2 H₀
    have h2 : 2 ∣ Nat.card (SecW X Y h) := by
      rcases (HeisMod.isPGroup_two hW2).card_eq_or_dvd with h1 | h1
      · exfalso
        rw [SecW.card] at h1
        exact hXY.ne (le_antisymm hXY.le (Subgroup.relIndex_eq_one.mp h1))
      · exact h1
    obtain ⟨b, hb, hb1⟩ := hQ2.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (SecW X Y h) h2 (a := 1) (fun q' => map_one (ρ (Subgroup.inclusion (pCoreOf_le 2 H₀) q')))
    intro hbot
    apply hb1
    have hbF : b ∈ F := (hmemF b).mpr fun q' => hb q'
    rw [hbot, Subgroup.mem_bot] at hbF
    exact hbF.symm
  have hpre := le_normalizer_pre_of_act h hFinv
  rcases hchief (SecW.pre h F) (SecW.le_pre h F) (SecW.pre_le h F) hpre with he | he
  · exfalso
    apply hF1
    rw [← SecW.img_pre h F, he]
    exact (SecW.img_eq_bot_iff h h.le).mpr le_rfl
  · have htop : F = ⊤ := by
      rw [← SecW.img_pre h F, he]
      exact (SecW.img_eq_top_iff h h.le le_rfl).mpr rfl
    ext w
    have hw : w ∈ F := htop ▸ Subgroup.mem_top w
    exact (hmemF w).mp hw ⟨q, hq⟩

end ChiefGen

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
  {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include E hF N

theorem chief_faithful {Z₀ Z : Subgroup G} (hUZ₀ : fsuU T V ≤ Z₀) (hZ₀Z : Z₀ < Z)
    (hZC : Z ≤ hz T V ⊓ Subgroup.centralizer (fsuU T V : Set G))
    (hZ₀n : hz T V ≤ Subgroup.normalizer (Z₀ : Set G))
    (hZn : hz T V ≤ Subgroup.normalizer (Z : Set G)) (hsec : IsElemSection Z Z₀)
    (hchief : ∀ X : Subgroup G, Z₀ ≤ X → X ≤ Z → hz T V ≤ Subgroup.normalizer (X : Set G) →
      X = Z₀ ∨ X = Z)
    (hnc : ¬ ⁅Z, oTwoUpper (hz T V)⁆ ≤ Z₀) :
    Z₀.relIndex Z = 64 ∧
      (∀ X : Subgroup G, Z₀ ≤ X → X ≤ Z → oTwoUpper (hz T V) ≤ Subgroup.normalizer (X : Set G) →
        X = Z₀ ∨ X = Z) ∧
      (∀ x ∈ hz T V, (∀ w ∈ Z, x * w * x⁻¹ * w⁻¹ ∈ Z₀) → x ∈ pCoreOf 2 (hz T V)) ∧
      4 ≤ Z₀.relIndex (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
        Subgroup.centralizer (fsuU T V : Set G) ⊓ Z) := by
  have hcomm_r := E.comm_r_q hF
  have hEαR := E.ealpha_le_r hF N
  have hcommEα := E.comm_mem_ealpha hF N
  obtain ⟨hVEα, hVEα4⟩ := E.relIndex_v_ealpha hF N
  obtain ⟨hH, -⟩ := E.lemma14_7_15_three_of hF
  subst hH
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVU : V ≤ fsuU T V := by
    rw [E.fsuU_eq]
    exact le_conjClosure V _
  obtain ⟨a, b, c, y, haK, hbK, hcL, hc1, hc3, hcz, -, hyT, hyC, hy2, hy4, huniq, hinv, -, habU,
    htaU, -, -, -⟩ := E.exists_frame hF
  have hρU := rhoDot_injective hF.toHypF91
  obtain ⟨s₀, hs₀, hab⟩ : ∃ s₀ : ℕ, s₀ % 3 ≠ 0 ∧ a * b = b * a * c ^ s₀ := by
    obtain ⟨s₀, hs₀, e⟩ := habU
    exact ⟨s₀, hs₀, hρU (by rw [map_mul, map_mul, map_mul, map_pow, e])⟩
  obtain ⟨k₀, hta⟩ : ∃ k₀ : ℕ, y ^ 2 * a * y ^ 2 = a⁻¹ * c ^ k₀ := by
    obtain ⟨k₀, e⟩ := htaU
    exact ⟨k₀, hρU (by rw [map_mul, map_mul, map_mul, map_inv, e, map_pow])⟩
  have hca : c * a = a * c := E.comm_of_mem_l1dot c hcL a haK
  have hcb : c * b = b * c := E.comm_of_mem_l1dot c hcL b hbK
  have hcy2 : c * y ^ 2 = y ^ 2 * c :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hyC 2) c hcL
  have ha3 : a ^ 3 = 1 := E.pow_three_of_mem_kdot haK
  have hb3 : b ^ 3 = 1 := E.pow_three_of_mem_kdot hbK
  have hcs : c ^ s₀ ≠ 1 := by
    have e : c ^ s₀ = c ^ (s₀ % 3) := by
      conv_lhs => rw [← Nat.mod_add_div s₀ 3, pow_add, pow_mul, hc3, one_pow, mul_one]
    rw [e]
    have hr : s₀ % 3 = 1 ∨ s₀ % 3 = 2 := by omega
    rcases hr with hr | hr
    · rw [hr, pow_one]
      exact hc1
    · rw [hr]
      intro h2
      apply hc1
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
        _ = 1 := by rw [hc3, h2]; group
  have hab_ne : a * b ≠ b * a := fun e => hcs (by
    have : b * a = b * a * c ^ s₀ := e ▸ hab
    exact (mul_eq_left.mp this.symm))
  have haL : a ∉ modO2Image (hz T V) (l1 T L V) := fun h =>
    hab_ne (E.comm_of_mem_l1dot a h b hbK)
  have hbL : b ∉ modO2Image (hz T V) (l1 T L V) := fun h =>
    hab_ne (E.comm_of_mem_l1dot b h a haK).symm
  have habL : a * b ∉ modO2Image (hz T V) (l1 T L V) := fun h => by
    have h1 := E.comm_of_mem_l1dot _ h a haK
    apply hab_ne
    have h2 : a * (b * a) = a * (a * b) := by rw [← mul_assoc, h1]
    exact (mul_left_cancel h2).symm
  have habbL : a * b * b ∉ modO2Image (hz T V) (l1 T L V) := fun h => by
    have h1 := E.comm_of_mem_l1dot _ h a haK
    have h2 : b * b * a = a * (b * b) := by
      have h3 : a * (b * b * a) = a * (a * (b * b)) := by
        calc a * (b * b * a) = a * b * b * a := by group
          _ = a * (a * b * b) := h1
          _ = a * (a * (b * b)) := by group
      exact mul_left_cancel h3
    apply hab_ne
    have hb4 : b = b * b * (b * b) := by
      calc b = b ^ 3 * b := by rw [hb3, one_mul]
        _ = b * b * (b * b) := by simp only [pow_three, mul_assoc]
    calc a * b = a * (b * b * (b * b)) := by rw [← hb4]
      _ = b * b * (b * b) * a := by rw [← mul_assoc, ← h2, mul_assoc, ← h2]; group
      _ = b * a := by rw [← hb4]
  have hbNa : b ∉ Subgroup.zpowers a ⊔ modO2Image (hz T V) (l1 T L V) := by
    have := E.l1dot_normal
    intro hmem
    obtain ⟨x, hx, l, hl, hxl⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    apply hab_ne
    have hla : l * a = a * l := E.comm_of_mem_l1dot l hl a haK
    rw [← hxl]
    calc a * (a ^ i * l) = a ^ i * (a * l) := by rw [← mul_assoc, ← zpow_one_add, add_comm,
          zpow_add_one, mul_assoc]
      _ = a ^ i * l * a := by rw [← hla, mul_assoc]
  set ρ := SecW.act hsec (hz T V) hZn hZ₀n with hρdef
  have hW2 : ∀ w : SecW Z Z₀ hsec, w * w = 1 := SecW.mul_self hsec
  have hQ : ∀ q (hq : q ∈ pCoreOf 2 (hz T V)), ρ ⟨q, pCoreOf_le 2 _ hq⟩ = 1 :=
    fun q hq => act_eq_one_of_chief hsec hZ₀Z hZn hZ₀n hchief hq
  let ρd : (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) →* MulAut (SecW Z Z₀ hsec) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥(hz T V)) ρ (fun x hx => by
      rw [MonoidHom.mem_ker]
      have hx' : (x : G) ∈ pCoreOf 2 (hz T V) := by
        rw [pCoreOf]
        exact ⟨x, hx, rfl⟩
      exact hQ _ hx')
  have hρd : ∀ x : ↥(hz T V), ρd (QuotientGroup.mk x) = ρ x := fun x => rfl
  have hne : ∃ w : SecW Z Z₀ hsec, w ≠ 1 := by
    obtain ⟨z, hz, hz0⟩ := IsConcreteLE.exists_of_lt hZ₀Z
    exact ⟨SecW.mk hsec ⟨z, hz⟩, fun h => hz0 ((SecW.mk_eq_one_iff hsec _).mp h)⟩
  have hyU := E.ualpha_eq hF N hy2 hy4 huniq
  obtain ⟨s, hsU, hsy⟩ := mem_modO2Image_iff.mp
    (show y ^ 2 ∈ modO2Image (hz T V) (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)))
      by rw [hyU]; exact Subgroup.mem_zpowers _)
  obtain ⟨-, -, -, hR1Q, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  have hyQ : y ∈ modO2Image (hz T V) (pCoreOf 2 (L ⊔ T)) := by
    rw [← hR1Q, hR1C]
    exact ⟨hyT, hyC⟩
  obtain ⟨q₀, hq₀Q, hq₀y⟩ := mem_modO2Image_iff.mp hyQ
  have hT : ρd (y ^ 2) = ρ s := by rw [← hsy]; rfl
  have hY : ρd y = ρ q₀ := by rw [← hq₀y]; rfl
  have hT2 : ρd (y ^ 2) * ρd (y ^ 2) = 1 := by rw [← map_mul, ← pow_add, hy4, map_one]
  have hwT : ∀ z (hz : z ∈ Z), SecW.mk hsec ⟨z, hz⟩ * ρd (y ^ 2) (SecW.mk hsec ⟨z, hz⟩) =
      SecW.mk hsec ⟨z⁻¹ * (s * z * s⁻¹), mul_mem (inv_mem hz)
        ((Subgroup.mem_normalizer_iff.mp (hZn s.2) z).mp hz)⟩ := by
    intro z hz
    rw [hT, hρdef, SecW.act_mk]
    have e1 : SecW.mk hsec ⟨z, hz⟩ = SecW.mk hsec ⟨z⁻¹, inv_mem hz⟩ := by
      have h1 := hW2 (SecW.mk hsec ⟨z, hz⟩)
      have h2 : SecW.mk hsec ⟨z⁻¹, inv_mem hz⟩ = (SecW.mk hsec ⟨z, hz⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [h2]
      exact (eq_inv_of_mul_eq_one_left h1)
    rw [e1, ← map_mul]
    rfl
  have hEZ : ∀ z ∈ Z, z⁻¹ * (s * z * s⁻¹) ∈ Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
      Subgroup.centralizer (fsuU T V : Set G) ⊓ Z := fun z hz =>
    Subgroup.mem_inf.mpr ⟨hcommEα z (hZC hz) s hsU, mul_mem (inv_mem hz)
      ((Subgroup.mem_normalizer_iff.mp (hZn s.2) z).mp hz)⟩
  have hcommle : commV (Subgroup.zpowers (ρd (y ^ 2))) ≤
      SecW.img hsec (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
        Subgroup.centralizer (fsuU T V : Set G) ⊓ Z) := by
    rw [HeisMod.commV_zpowers_eq_range hW2 hT2]
    rintro _ ⟨w, rfl⟩
    obtain ⟨⟨z, hz⟩, rfl⟩ := SecW.mk_surjective hsec w
    rw [HeisMod.trHom_apply, hwT z hz]
    exact SecW.mk_mem_img hsec (hEZ z hz)
  have hcard_le : Nat.card (commV (Subgroup.zpowers (ρd (y ^ 2)))) ≤ 4 := by
    have h1 := Subgroup.card_le_of_le hcommle
    rw [SecW.card_img hsec inf_le_right] at h1
    have h2 : Z₀.relIndex (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
        Subgroup.centralizer (fsuU T V : Set G) ⊓ Z) ≤
        V.relIndex (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
          Subgroup.centralizer (fsuU T V : Set G) ⊓ Z) :=
      Subgroup.relIndex_le_of_le_left (hVU.trans hUZ₀) (by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite)
    have h3 : V.relIndex (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
        Subgroup.centralizer (fsuU T V : Set G) ⊓ Z) ≤
        V.relIndex (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊓
          Subgroup.centralizer (fsuU T V : Set G)) :=
      Subgroup.relIndex_le_of_le_right inf_le_left (by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite)
    omega
  have hYfix : ∀ w : SecW Z Z₀ hsec, ρd y (w * ρd (y ^ 2) w) = w * ρd (y ^ 2) w := by
    intro w
    obtain ⟨⟨z, hz⟩, rfl⟩ := SecW.mk_surjective hsec w
    rw [hwT z hz, hY]
    refine (SecW.act_mk_eq_mk_iff hsec q₀ _).mpr ?_
    have hrR := hEαR (hEZ z hz).1
    have hc := Subgroup.commutator_mem_commutator hq₀Q hrR
    rw [Subgroup.commutator_comm, hcomm_r, commutatorElement_def] at hc
    exact hUZ₀ (hVU hc)
  have hstab : ∀ w : SecW Z Z₀ hsec, ∃ S : Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)),
      ∀ x, x ∈ S ↔ ρd x w = w := fun w =>
    ⟨{ carrier := {x | ρd x w = w}
       mul_mem' := fun {x x'} hx hx' => by
         change ρd x w = w at hx
         change ρd x' w = w at hx'
         change ρd (x * x') w = w
         rw [map_mul, MulAut.mul_apply, hx', hx]
       one_mem' := by
         change ρd 1 w = w
         rw [map_one, MulAut.one_apply]
       inv_mem' := fun {x} hx => by
         change ρd x w = w at hx
         change ρd x⁻¹ w = w
         rw [map_inv]
         calc (ρd x)⁻¹ w = (ρd x)⁻¹ (ρd x w) := by rw [hx]
           _ = w := MulAut.inv_apply_self _ _ _ }, fun x => Iff.rfl⟩
  have hL1 : ρd c = 1 → ∀ l ∈ modO2Image (hz T V) (l1 T L V), ρd l = 1 := by
    intro hc l hl
    rw [← hcz] at hl
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
    rw [map_zpow, hc, one_zpow]
  have hexcl : ρd c ≠ 1 := by
    intro hc
    have hTi : (ρd (y ^ 2))⁻¹ = ρd (y ^ 2) := inv_eq_of_mul_eq_one_left hT2
    have hTA : ρd (y ^ 2) * ρd a * ρd (y ^ 2) = (ρd a)⁻¹ := by
      rw [← map_mul, ← map_mul, hta, map_mul, map_inv, map_pow, hc, one_pow, mul_one]
    have hTB : ρd (y ^ 2) * ρd b * ρd (y ^ 2) = (ρd b)⁻¹ := by
      have h1 := hL1 hc _ (hinv b hbK)
      rw [map_mul, map_mul, map_mul, map_inv, hTi] at h1
      exact eq_inv_of_mul_eq_one_left h1
    have hAB : ρd a * ρd b = ρd b * ρd a := by
      rw [← map_mul, hab, map_mul, map_mul, map_pow, hc, one_pow, mul_one]
    have hA3 : ρd a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    have hB3 : ρd b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
    have hline : ∀ g' : MulAut (SecW Z Z₀ hsec),
        (g' = ρd a ∨ g' = ρd b ∨ g' = ρd a * ρd b ∨ g' = ρd a * ρd b * ρd b) →
        ∀ w, g' w = w → (ρd y * g' * (ρd y)⁻¹) w = w → ρd a w = w ∧ ρd b w = w := by
      intro g' hg' w hw1 hw2
      obtain ⟨g₀, hg₀K, hg₀L, rfl⟩ : ∃ g₀, g₀ ∈ modO2Image (hz T V) (oTwoUpper (hz T V)) ∧
          g₀ ∉ modO2Image (hz T V) (l1 T L V) ∧ g' = ρd g₀ := by
        rcases hg' with rfl | rfl | rfl | rfl
        · exact ⟨a, haK, haL, rfl⟩
        · exact ⟨b, hbK, hbL, rfl⟩
        · exact ⟨a * b, mul_mem haK hbK, habL, (map_mul _ _ _).symm⟩
        · exact ⟨a * b * b, mul_mem (mul_mem haK hbK) hbK, habbL, by rw [map_mul, map_mul]⟩
      obtain ⟨S, hS⟩ := hstab w
      have hle := E.kdot_le_closure_conj hyC hinv hg₀K hg₀L
      have hcl : Subgroup.closure {g₀, y * g₀ * y⁻¹} ⊔ modO2Image (hz T V) (l1 T L V) ≤ S := by
        refine sup_le ((Subgroup.closure_le S).mpr ?_) fun l hl =>
          (hS l).mpr (by rw [hL1 hc l hl]; rfl)
        rintro x (rfl | rfl)
        · exact (hS _).mpr hw1
        · refine (hS _).mpr ?_
          rw [map_mul, map_mul, map_inv]
          exact hw2
      exact ⟨(hS a).mp (hcl (hle haK)), (hS b).mp (hcl (hle hbK))⟩
    obtain ⟨hA1, hB1⟩ := HeisMod.eq_one_of_fix_commV hW2 hA3 hB3 hAB hT2 hTA hTB hYfix hline
    apply hnc
    have hKtriv : ∀ x ∈ modO2Image (hz T V) (oTwoUpper (hz T V)), ρd x = 1 := by
      have hle := E.kdot_le_closure_pair haK haL hbK hbNa
      have hcl : Subgroup.closure {a, b} ⊔ modO2Image (hz T V) (l1 T L V) ≤ ρd.ker := by
        refine sup_le ((Subgroup.closure_le _).mpr ?_) fun l hl =>
          MonoidHom.mem_ker.mpr (hL1 hc l hl)
        rintro x (rfl | rfl)
        · exact MonoidHom.mem_ker.mpr hA1
        · exact MonoidHom.mem_ker.mpr hB1
      exact fun x hx => MonoidHom.mem_ker.mp (hcl (hle hx))
    rw [Subgroup.commutator_le]
    intro z hzZ x hx
    have hxH : x ∈ hz T V := oTwoUpper_le _ hx
    have h1 : ρ ⟨x, hxH⟩ = 1 := hKtriv _ (mem_modO2Image_iff.mpr ⟨⟨x, hxH⟩, hx, rfl⟩)
    have h2 := (SecW.act_eq_one_iff hsec ⟨x, hxH⟩).mp h1 z⁻¹ (inv_mem hzZ)
    have h3 : z * (x * z⁻¹ * x⁻¹ * z⁻¹⁻¹) * z⁻¹ ∈ Z₀ :=
      (Subgroup.mem_normalizer_iff.mp (hZ₀n (hZC hzZ).1) _).mp h2
    rw [commutatorElement_def]
    have e : z * x * z⁻¹ * x⁻¹ = z * (x * z⁻¹ * x⁻¹ * z⁻¹⁻¹) * z⁻¹ := by group
    rw [e]
    exact h3
  have hfpf : ∀ w, ρd c w = w → w = 1 := by
    have hinvC : ∀ x : ↥(hz T V), ∀ w ∈ fixSub (ρd c), ρ x w ∈ fixSub (ρd c) := by
      intro x w hw
      rw [mem_fixSub] at hw ⊢
      have := E.l1dot_normal
      have hxc : (QuotientGroup.mk x : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))⁻¹ * c *
          (QuotientGroup.mk x : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))⁻¹⁻¹ ∈
          Subgroup.zpowers c := by
        rw [hcz]
        exact this.conj_mem c hcL _
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hxc
      rw [inv_inv] at hi
      have e : c * (QuotientGroup.mk x : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) =
          QuotientGroup.mk x * c ^ i := by
        rw [hi]
        group
      obtain ⟨S, hS⟩ := hstab w
      have hci : c ^ i ∈ S := S.zpow_mem ((hS c).mpr hw) i
      calc ρd c (ρ x w) = ρd (c * QuotientGroup.mk x) w := by
            rw [map_mul]
            rfl
        _ = ρd (QuotientGroup.mk x * c ^ i) w := by rw [e]
        _ = ρ x (ρd (c ^ i) w) := by
            rw [map_mul]
            rfl
        _ = ρ x w := by rw [(hS _).mp hci]
    have hpre := le_normalizer_pre_of_act hsec hinvC
    rcases hchief _ (SecW.le_pre hsec _) (SecW.pre_le hsec _) hpre with he | he
    · intro w hw
      have hw' : w ∈ fixSub (ρd c) := hw
      rw [← SecW.img_pre hsec (fixSub (ρd c)), he,
        (SecW.img_eq_bot_iff hsec hsec.le).mpr le_rfl] at hw'
      exact hw'
    · exfalso
      apply hexcl
      have htop : fixSub (ρd c) = ⊤ := by
        rw [← SecW.img_pre hsec (fixSub (ρd c)), he]
        exact (SecW.img_eq_top_iff hsec hsec.le le_rfl).mpr rfl
      ext w
      have hw : w ∈ fixSub (ρd c) := htop ▸ Subgroup.mem_top w
      exact hw
  have hc3' : ρd c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have ha3' : ρd a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hac' : ρd a * ρd c = ρd c * ρd a := by rw [← map_mul, ← hca, map_mul]
  have hbc' : ρd b * ρd c = ρd c * ρd b := by rw [← map_mul, ← hcb, map_mul]
  have hab' : ρd a * ρd b = ρd b * ρd a * ρd c ^ s₀ := by
    rw [← map_mul, hab, map_mul, map_mul, map_pow]
  have htc' : ρd (y ^ 2) * ρd c = ρd c * ρd (y ^ 2) := by rw [← map_mul, ← hcy2, map_mul]
  have hta' : ρd (y ^ 2) * ρd a * ρd (y ^ 2) = (ρd a)⁻¹ * ρd c ^ k₀ := by
    rw [← map_mul, ← map_mul, hta, map_mul, map_inv, map_pow]
  obtain ⟨h64, hwt, h4⟩ := HeisMod.card_eq_sixtyfour hW2 hc3' hfpf ha3' hac' hbc' hab' hs₀ hT2
    htc' hta' hne hcard_le
  refine ⟨by rw [← SecW.card hsec]; exact h64, fun X hZ₀X hXZ hKX => ?_, fun x hx hxw => ?_, ?_⟩
  ·
    have hinvX : ∀ x : ↥(hz T V), (x : G) ∈ oTwoUpper (hz T V) → ∀ w ∈ SecW.img hsec X,
        ρ x w ∈ SecW.img hsec X := fun x hx w hw => SecW.act_mem_img hsec x (hKX hx) hw
    obtain ⟨a', ha'K, ha'⟩ := mem_modO2Image_iff.mp haK
    obtain ⟨b', hb'K, hb'⟩ := mem_modO2Image_iff.mp hbK
    obtain ⟨c', hc'L, hc'⟩ := mem_modO2Image_iff.mp hcL
    obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
    have hXa : ∀ w ∈ SecW.img hsec X, ρd a w ∈ SecW.img hsec X := by
      rw [← ha']
      exact hinvX a' ha'K
    have hXb : ∀ w ∈ SecW.img hsec X, ρd b w ∈ SecW.img hsec X := by
      rw [← hb']
      exact hinvX b' hb'K
    have hXc : ∀ w ∈ SecW.img hsec X, ρd c w ∈ SecW.img hsec X := by
      rw [← hc']
      exact hinvX c' (hL1K hc'L)
    by_cases hb : SecW.img hsec X = ⊥
    · left
      exact le_antisymm ((SecW.img_eq_bot_iff hsec hXZ).mp hb) hZ₀X
    · right
      exact (SecW.img_eq_top_iff hsec hZ₀X hXZ).mp
        (HeisMod.eq_top_of_invariant hW2 hc3' hfpf ha3' hac' hbc' hab' hs₀ hwt hXa hXb hXc hb)
  ·
    have h1 : ρd (QuotientGroup.mk ⟨x, hx⟩) = 1 := (SecW.act_eq_one_iff hsec ⟨x, hx⟩).mpr hxw
    have hKN : ∀ m ∈ modO2Image (hz T V) (oTwoUpper (hz T V)), ρd m = 1 → m = 1 := by
      intro m hmK hm
      by_contra hm1
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hnorm : (ρd.ker.subgroupOf (modO2Image (hz T V) (oTwoUpper (hz T V)))).Normal :=
        Subgroup.Normal.subgroupOf (MonoidHom.normal_ker ρd) _
      have hK3 : IsPGroup 3 ↥(modO2Image (hz T V) (oTwoUpper (hz T V))) :=
        IsPGroup.of_card (n := 3) (by rw [E.card_kdot]; norm_num)
      have : Group.IsNilpotent ↥(modO2Image (hz T V) (oTwoUpper (hz T V))) := hK3.isNilpotent
      have hne' : ρd.ker.subgroupOf (modO2Image (hz T V) (oTwoUpper (hz T V))) ≠ ⊥ := by
        intro hb
        have hmem : (⟨m, hmK⟩ : ↥(modO2Image (hz T V) (oTwoUpper (hz T V)))) ∈
            ρd.ker.subgroupOf (modO2Image (hz T V) (oTwoUpper (hz T V))) := hm
        rw [hb, Subgroup.mem_bot] at hmem
        exact hm1 (congrArg Subtype.val hmem)
      obtain ⟨⟨z, hzN, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
        (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
      have hzL : (z : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) ∈ modO2Image (hz T V) (l1 T L V) := by
        rw [← E.exists_y.1]
        exact ⟨z, hzZ, rfl⟩
      have hz1' : (z : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) ≠ 1 := fun e =>
        hz1 (Subtype.ext (Subtype.ext e))
      have hle : Subgroup.zpowers (z : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) ≤
          modO2Image (hz T V) (l1 T L V) := (Subgroup.zpowers_le).mpr hzL
      have hd := Subgroup.card_dvd_of_le hle
      rw [E.card_l1dot] at hd
      have h1' : Nat.card (Subgroup.zpowers (z : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) ≠ 1 := by
        rw [Nat.card_zpowers]
        exact fun h => hz1' (orderOf_eq_one_iff.mp h)
      have h3 := (Nat.prime_three.eq_one_or_self_of_dvd _ hd).resolve_left h1'
      have hzpow := Subgroup.eq_of_le_of_card_ge hle (by rw [h3, E.card_l1dot])
      have hcz' : c ∈ Subgroup.zpowers (z : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) := hzpow ▸ hcL
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hcz'
      apply hexcl
      have hzk : ρd (z : ↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) = 1 :=
        MonoidHom.mem_ker.mp (Subgroup.mem_subgroupOf.mp hzN)
      rw [← hi, map_zpow, hzk, one_zpow]
    have hker : ∀ n, ρd n = 1 → n = 1 := by
      intro n hn
      have hcent : n ∈ Subgroup.centralizer ((modO2Image (hz T V) (oTwoUpper (hz T V)) :
          Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
            Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) := by
        refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
        have h1 : n * x * n⁻¹ * x⁻¹ ∈ modO2Image (hz T V) (oTwoUpper (hz T V)) :=
          mul_mem (E.kdot_normal.conj_mem x hx n) (inv_mem hx)
        have h2 : ρd (n * x * n⁻¹ * x⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hn]
          group
        have h3 := hKN _ h1 h2
        calc x * n = (n * x * n⁻¹ * x⁻¹)⁻¹ * n * x := by group
          _ = n * x := by rw [h3]; group
      obtain ⟨e, he⟩ := E.isPGroup_centralizer ⟨n, hcent⟩
      have hnK : n ∈ modO2Image (hz T V) (oTwoUpper (hz T V)) :=
        E.mem_kdot_of_pow hF (m := e) (by simpa using congrArg Subtype.val he)
      exact hKN n hnK hn
    have h2 := hker _ h1
    rw [QuotientGroup.eq_one_iff] at h2
    exact ⟨_, h2, rfl⟩
  · have h1 := Subgroup.card_le_of_le hcommle
    rw [SecW.card_img hsec inf_le_right, h4] at h1
    exact h1

end Ctx7153

end CFSG.Quasithin.H13.L32A
