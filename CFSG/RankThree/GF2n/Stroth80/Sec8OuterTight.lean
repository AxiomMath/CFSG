module

public import CFSG.RankThree.GF2n.Stroth80.Sec8TypeCount
public import CFSG.RankThree.GF2n.Stroth80.Sec8Canon
public import CFSG.RankThree.GF2n.Stroth80.Sec8OuterElt

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

section Count

variable {G : Type} [Group G] [Finite G]

theorem sec8_card_inf_le_of_comm_section {R P I U T : Subgroup G} {Mo : Type} [AddCommGroup Mo]
    [DistribMulAction ↥R Mo] {κ : ↥P →* Multiplicative Mo}
    (hκ : IsSecMod R P I Mo κ) (hIU : I ≤ U) (hUP : U ≤ P) (hTP : T ≤ P)
    (hUT : ∀ y ∈ U, ∃ w ∈ T, y * w⁻¹ ∈ I) :
    Nat.card ↥U * Nat.card ↥(T ⊓ I) ≤ Nat.card ↥T * Nat.card ↥I := by
  haveI : Finite Mo := hκ.finite
  have hle : secSub κ U ≤ secSub κ T := by
    intro a ha
    obtain ⟨y, hyU, hya⟩ := mem_secSub.mp ha
    obtain ⟨w, hwT, hyw⟩ := hUT (y : G) hyU
    exact mem_secSub.mpr ⟨⟨w, hTP hwT⟩, hwT,
      ((hκ.eq_iff y ⟨w, hTP hwT⟩).mpr hyw).symm.trans hya⟩
  have hsec : Nat.card ↥(secSub κ U) ≤ Nat.card ↥(secSub κ T) :=
    AddSubgroup.card_le_of_le hle
  have hT : Nat.card ↥(secSub κ T) * Nat.card ↥(T ⊓ I) = Nat.card ↥T := by
    have hker : κ.ker = I.subgroupOf P := by
      ext x
      rw [MonoidHom.mem_ker, hκ.ker, Subgroup.mem_subgroupOf]
    have h1 : Nat.card ↥(secSub κ T) = Nat.card ↥((T.subgroupOf P).map κ) :=
      Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun a => Iff.rfl))
    have h2 := card_inf_mul_card_map hTP κ hker
    rw [h1, mul_comm]
    exact h2
  have hU : Nat.card ↥(secSub κ U) * Nat.card ↥I = Nat.card ↥U :=
    natCard_secSub_mul (hIU.trans hUP) hκ hIU hUP
  calc Nat.card ↥U * Nat.card ↥(T ⊓ I)
      = (Nat.card ↥(secSub κ U) * Nat.card ↥I) * Nat.card ↥(T ⊓ I) := by rw [hU]
    _ ≤ (Nat.card ↥(secSub κ T) * Nat.card ↥I) * Nat.card ↥(T ⊓ I) :=
        Nat.mul_le_mul (Nat.mul_le_mul hsec le_rfl) le_rfl
    _ = (Nat.card ↥(secSub κ T) * Nat.card ↥(T ⊓ I)) * Nat.card ↥I := by ring
    _ = Nat.card ↥T * Nat.card ↥I := by rw [hT]

theorem sec8_tight_arith {q a x T : ℕ} (hq : 2 ≤ q) (ha : 1 ≤ a) (hxq : q ≤ x)
    (h1 : q ^ (4 * a) * x ≤ T) (hT : T ≤ q ^ 5) : a = 1 ∧ x = q ∧ T = q ^ 5 := by
  have hqpos : 0 < q := by omega
  have h2 : q ^ (4 * a + 1) ≤ q ^ 5 := by
    calc q ^ (4 * a + 1) = q ^ (4 * a) * q := pow_succ _ _
      _ ≤ q ^ (4 * a) * x := Nat.mul_le_mul_left _ hxq
      _ ≤ T := h1
      _ ≤ q ^ 5 := hT
  have h3 : 4 * a + 1 ≤ 5 := (Nat.pow_le_pow_iff_right hq).mp h2
  have ha1 : a = 1 := by omega
  subst ha1
  have h4 : q ^ 4 * x ≤ q ^ 4 * q := by
    calc q ^ 4 * x ≤ T := by simpa using h1
      _ ≤ q ^ 5 := hT
      _ = q ^ 4 * q := pow_succ _ _
  have h5 : x ≤ q := Nat.le_of_mul_le_mul_left h4 (by positivity)
  have hx : x = q := le_antisymm h5 hxq
  subst hx
  refine ⟨rfl, rfl, le_antisymm hT ?_⟩
  calc x ^ 5 = x ^ 4 * x := pow_succ _ _
    _ ≤ T := by simpa using h1

end Count

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_outer_tight (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement) {hc : Ctx M Q Z B} {n : ℕ}
    {t r g : G} (h : Sec8Outer hc n t r g) {m : ℕ} (hmSp : SpMNat hc t m) :
    m = 2 ∧ conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Sec8W1 M Q Z B t r ∧
      conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8V1 M Q Z B t r = Z := by
  classical
  have hs := h.hs
  have hr := h.hr
  have hgM := h.hg
  have hxt := h.hxt
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  obtain ⟨K, fK, finK, hchar, φ, hn, ψ, u, u', hpts, -⟩ := sec8_natdata h34 hRoot hs hr hmSp
  haveI := hn
  haveI := hchar
  have hm2 : 2 ≤ m := hpts.two_le
  have hVV₁ : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r := le_inf le_sup_right le_sup_right
  have hZV₁ : Z ≤ Sec8V1 M Q Z B t r := sec8_Z_le_V1 hc t r
  have hInv := fun ρ hρ => sec8InvStatement_holds G M Q Z B hc n t hs r hr ρ hρ
  have hP : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Sec8W1 M Q Z B t r,
      ρ * y * ρ⁻¹ ∈ Sec8W1 M Q Z B t r :=
    fun ρ hρ y hy => conj_mem_of_conjSubgroup_eq (hInv ρ hρ).2 hy
  have hI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Sec8V1 M Q Z B t r,
      ρ * y * ρ⁻¹ ∈ Sec8V1 M Q Z B t r :=
    fun ρ hρ y hy => conj_mem_of_conjSubgroup_eq (hInv ρ hρ).1 hy
  have h53b := h53.2.1 G M Q Z B hc n t hs5 hs.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl
  have h53c := h53.2.2.1 G M Q Z B hc n t hs5 hs.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hsec : SecHyp (Rt M (LB M Q B) t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) :=
    SecHyp.of_isOppDecomp h53c hP hI
  have hxV : g * t * g⁻¹ ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    sec8_normV_of_comm hc hxM hxt
  have hVx : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z :=
    fun v hv => h.hvan v (hVV₁ hv)
  have hxc : ∀ ρ ∈ Rt M (LB M Q B) t, ρ * (g * t * g⁻¹) * ρ⁻¹ * (g * t * g⁻¹)⁻¹ ∈ hc.CN t :=
    fun ρ hρ => sec8_comm_mem_CN hc ht hxM hxt hVx hρ
  have hxN : g * t * g⁻¹ ∈ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) :=
    sec8Canon_of h34 hRoot G M Q Z B hc n t hs r hr _ hxM hxV
  have hxWn : g * t * g⁻¹ ∈ Subgroup.normalizer (Sec8W1 M Q Z B t r : Set G) :=
    sec8_Wt_mem_normalizer (hc.hyp.Q_normal.2 hxM) hxN
  have hxP : ∀ y ∈ Sec8W1 M Q Z B t r, (g * t * g⁻¹) * y * (g * t * g⁻¹)⁻¹ ∈
      Sec8W1 M Q Z B t r := fun y hy => (Subgroup.mem_normalizer_iff.mp hxWn y).mp hy
  obtain ⟨U, hIU, hUP, hUinv, hUx, hUcov⟩ :=
    sec8_exists_comm_section hsec hxP hxc h53b.2
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hpts.hL'
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLCR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem ht hrR
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  obtain ⟨-, a, ha⟩ := sec8_invariant_section (R := Rt M (LB M Q B) t) (N := hc.CN t)
    (P := Sec8W1 M Q Z B t r) (I := Sec8V1 M Q Z B t r) (L₁ := LB M Q B)
    (L₂ := LB M Q (conjSubgroup r B))
    (A₁ := (QB B ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r)
    (A₂ := (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r) ⊔ Sec8V1 M Q Z B t r) (U := U) φ
    hpts.range (by omega) hpts.ker hP hI h53b.2 h53c hLR hLCR hpts.uu' hpts.u_ne_zero hpts.hL hL2
    (fun y hy => hQN (hc.sq_mem_Q_of_mem_LB hy)) hrR (hc.LB_conj hrM).symm hIU hUP hUinv
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  obtain ⟨w₀, hw₀, hw₀V⟩ := h.hout
  have ha1 : 1 ≤ a := by
    by_contra h0
    have h00 : a = 0 := by omega
    rw [h00, mul_zero, pow_zero, mul_one] at ha
    have hUeq : Sec8V1 M Q Z B t r = U := Subgroup.eq_of_le_of_card_ge hIU ha.le
    exact hw₀V (hUeq ▸ hUx w₀ hw₀)
  have hV : Vt M (LB M Q B) B Z t = Ut Q Z t :=
    (h310chi G M Q Z B hc n t hs5 (Or.inl hs.spNat)).1
  have hVg : conjSubgroup g (Vt M (LB M Q B) B Z t) = Ut Q Z (g * t * g⁻¹) :=
    sec8_conj_V_eq_Ut hc hV hgM
  have hZg : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    (hc.conj_Z_eq hgM).symm.le.trans (Subgroup.map_mono sec39_Z_le_Vt)
  have hZT : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r :=
    le_inf hZg (sec8_Z_le_W1 hc t r)
  have hUT : ∀ y ∈ U, ∃ w ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r,
      y * w⁻¹ ∈ Sec8V1 M Q Z B t r := by
    intro y hy
    obtain ⟨w, hw, hyw⟩ := hUcov y hy
    refine ⟨⁅g * t * g⁻¹, w⁆, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, hyw⟩
    · rw [hVg]
      exact sec8_comm_mem_Ut (sec8_W1_le_Q M Q Z B t r hw)
    · exact sec8_comm_mem_of_conj_mem (hxP w hw) hw
  obtain ⟨Mo, iMo, iAct, κ, hκ⟩ := exists_sectionModule hsec
  have hcard := sec8_card_inf_le_of_comm_section hκ hIU hUP inf_le_right hUT
  have hTcard : Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r) ≤
      Nat.card Z ^ (2 * m + 1) := by
    calc Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r)
        ≤ Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t)) :=
          Subgroup.card_le_of_le inf_le_left
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) := card_conjSubgroup g _
      _ = Nat.card Z ^ (2 * m + 1) := hmSp.card_V
  have hxle : Nat.card Z ≤ Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓
      Sec8W1 M Q Z B t r ⊓ Sec8V1 M Q Z B t r) :=
    Subgroup.card_le_of_le (le_inf hZT hZV₁)
  rw [ha, hpts.card] at hcard
  have hpos : 0 < Nat.card ↥(Sec8V1 M Q Z B t r) := Nat.card_pos
  have hcard' : Nat.card Z ^ (2 ^ m * a) *
      Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r ⊓
        Sec8V1 M Q Z B t r) ≤
      Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r) := by
    have h2 : Nat.card ↥(Sec8V1 M Q Z B t r) * (Nat.card Z ^ (2 ^ m * a) *
        Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r ⊓
          Sec8V1 M Q Z B t r)) ≤
        Nat.card ↥(Sec8V1 M Q Z B t r) *
          Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r) := by
      calc Nat.card ↥(Sec8V1 M Q Z B t r) * (Nat.card Z ^ (2 ^ m * a) *
            Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r ⊓
              Sec8V1 M Q Z B t r))
          = Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Z ^ (2 ^ m * a) *
            Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r ⊓
              Sec8V1 M Q Z B t r) := by ring
        _ ≤ Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r) *
            Nat.card ↥(Sec8V1 M Q Z B t r) := hcard
        _ = Nat.card ↥(Sec8V1 M Q Z B t r) *
            Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r) := by ring
    exact Nat.le_of_mul_le_mul_left h2 hpos
  have hm : m = 2 := by
    have h1 : Nat.card Z ^ (2 ^ m * a) * Nat.card Z ≤ Nat.card Z ^ (2 * m + 1) :=
      calc Nat.card Z ^ (2 ^ m * a) * Nat.card Z
          ≤ Nat.card Z ^ (2 ^ m * a) *
            Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r ⊓
              Sec8V1 M Q Z B t r) := Nat.mul_le_mul_left _ hxle
        _ ≤ _ := hcard'
        _ ≤ _ := hTcard
    rw [← pow_succ] at h1
    exact sec8_m_eq_two_of_pow_le hm2 ha1 hq2 h1
  subst hm
  obtain ⟨-, hx, hT⟩ := sec8_tight_arith (q := Nat.card Z) (a := a) hq2 ha1 hxle
    (by simpa [mul_comm] using hcard') (by simpa using hTcard)
  have hTeq : conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r =
      conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [card_conjSubgroup, hmSp.card_V]
    exact le_of_eq hT.symm
  have hVgW : conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Sec8W1 M Q Z B t r := by
    rw [← hTeq]
    exact inf_le_right
  refine ⟨rfl, hVgW, ?_⟩
  have e : conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8V1 M Q Z B t r =
      conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8W1 M Q Z B t r ⊓ Sec8V1 M Q Z B t r := by
    rw [hTeq]
  have hx' : Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Sec8V1 M Q Z B t r) =
      Nat.card Z := by
    rw [e]
    exact hx
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hZg hZV₁) hx'.le).symm

end

end CFSG.RankThree.GF2n.Stroth80
