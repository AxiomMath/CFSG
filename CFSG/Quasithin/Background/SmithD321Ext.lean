module

public import CFSG.Quasithin.Background.SmithD321Kplus
public import CFSG.Quasithin.Background.SmithD321Three
public import CFSG.Quasithin.Background.F918D4
public import CFSG.Quasithin.Background.F918D2
public import CFSG.Quasithin.Background.SmithD310UCaseI

public section

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391
  CFSG.Assembly.LowTwoRank
open scoped Pointwise

namespace CFSG.Quasithin.SmithD321

section Orbit

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem card_modEq_card_inf_fixed [Finite Q] {p n : ℕ} [Fact p.Prime] {y : Γ}
    {S : Subgroup Q} (hy : ∀ s ∈ S, y ^ p ^ n • s = s) (hSy : ∀ s ∈ S, y • s ∈ S) :
    Nat.card ↥S ≡ Nat.card ↥(S ⊓ XMod.fixed ↥(Subgroup.zpowers y) (⊤ : Subgroup Q)) [MOD p] := by
  classical
  have := Fintype.ofFinite ↥S
  let f : Function.End ↥S := fun s => ⟨y • (s : Q), hSy s s.2⟩
  have hfk : ∀ k : ℕ, ∀ s : ↥S, ((f ^ k) s : Q) = y ^ k • (s : Q) := by
    intro k
    induction k with
    | zero => intro s; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ k ih =>
      intro s
      rw [pow_succ', pow_succ', mul_smul, ← ih]
      rfl
  have hf : f ^ p ^ n = 1 := by
    funext s
    apply Subtype.ext
    rw [hfk, hy s s.2]
    rfl
  have h1 := Equiv.Perm.card_fixedPoints_modEq hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h1
  have h2 : Nat.card ↑(Function.fixedPoints f) =
      Nat.card ↥(S ⊓ XMod.fixed ↥(Subgroup.zpowers y) (⊤ : Subgroup Q)) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨(s.1 : Q), s.1.2, ?_⟩
        invFun := fun s => ⟨⟨(s : Q), s.2.1⟩, ?_⟩
        left_inv := fun s => rfl
        right_inv := fun s => rfl }
    · refine (mem_fixed_zpowers_iff (b := y)).2 ?_
      have := s.2
      exact congrArg Subtype.val this
    · apply Subtype.ext
      exact (mem_fixed_zpowers_iff (b := y)).1 s.2.2
  rw [← h2]
  exact h1

theorem two_pow_mod_five (n : ℕ) : 2 ^ n % 5 = 2 ^ (n % 4) % 5 := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem eq_of_two_pow_modEq_five {m c j : ℕ} (hm : Odd m) (hjc : j ≤ c) (hc : c ≤ 4)
    (h : 2 ^ (c * m) ≡ 2 ^ (j * m) [MOD 5]) : j = c ∨ (j = 0 ∧ c = 4) := by
  unfold Nat.ModEq at h
  rw [two_pow_mod_five (c * m), two_pow_mod_five (j * m), Nat.mul_mod c, Nat.mul_mod j] at h
  have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by
    obtain ⟨k, rfl⟩ := hm
    omega
  interval_cases c <;> interval_cases j <;> rcases hm4 with h4 | h4 <;> rw [h4] at h <;>
    revert h <;> norm_num

theorem eq_bot_or_eq_of_pow_five [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) (hIodd : Odd (rk ↥I))
    (hY : IsotypicOfLength ↥Λ Y I 4) {y : Γ} (hyΛ : ∀ l ∈ Λ, y * l = l * y)
    (hy5 : ∀ q ∈ Y, y ^ 5 • q = q) (hyY : ∀ q ∈ Y, y • q ∈ Y) (hy1 : ∃ q ∈ Y, y • q ≠ q)
    {S : Subgroup Q} (hSY : S ≤ Y) (hSΛ : XMod.IsInv ↥Λ S) (hSy : ∀ s ∈ S, y • s ∈ S) :
    S = ⊥ ∨ S = Y := by
  have hy5' : ∀ q ∈ Y, y ^ 5 ^ 1 • q = q := by rw [pow_one]; exact hy5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set F := XMod.fixed ↥(Subgroup.zpowers y) (⊤ : Subgroup Q) with hF
  have hFΛ : XMod.IsInv ↥Λ F := by
    intro l q hq
    refine (mem_fixed_zpowers_iff (b := y)).2 ?_
    have hq' := (mem_fixed_zpowers_iff (b := y)).1 hq
    show y • ((l : Γ) • q) = (l : Γ) • q
    rw [smul_smul, hyΛ l l.2, mul_smul, hq']
  have key : ∀ R : Subgroup Q, R ≤ Y → XMod.IsInv ↥Λ R → (∀ r ∈ R, y • r ∈ R) →
      ∃ c j : ℕ, rk ↥R = c * rk ↥I ∧ rk ↥(R ⊓ F) = j * rk ↥I ∧ j ≤ c ∧ c ≤ 4 ∧
        (j = c ∨ (j = 0 ∧ c = 4)) := by
    intro R hRY hRΛ hRy
    obtain ⟨c, hc⟩ := exists_rk_eq_mul hQ hI hRΛ (hRY.trans hY.2.1)
    obtain ⟨j, hj⟩ := exists_rk_eq_mul hQ hI (hRΛ.inf hFΛ)
      ((inf_le_left.trans hRY).trans hY.2.1)
    have hI0 : 0 < rk ↥I := hIodd.pos
    have hjc : j ≤ c := by
      have := rk_mono (inf_le_left : R ⊓ F ≤ R)
      rw [hc, hj] at this
      exact Nat.le_of_mul_le_mul_right this hI0
    have hc4 : c ≤ 4 := by
      have := rk_mono hRY
      rw [hc, hY.2.2] at this
      exact Nat.le_of_mul_le_mul_right this hI0
    have hmod := card_modEq_card_inf_fixed (fun s hs => hy5' s (hRY hs)) hRy
    rw [card_eq_two_pow hQ, card_eq_two_pow hQ, hc, hj] at hmod
    exact ⟨c, j, hc, hj, hjc, hc4, eq_of_two_pow_modEq_five hIodd hjc hc4 hmod⟩
  have hYF : Y ⊓ F = ⊥ := by
    obtain ⟨c, j, hc, hj, -, -, hcj⟩ := key Y le_rfl hY.1 hyY
    have hc4 : c = 4 := by
      have hI0 : 0 < rk ↥I := hIodd.pos
      rw [hY.2.2] at hc
      exact (Nat.eq_of_mul_eq_mul_right hI0 hc).symm
    rcases hcj with h | ⟨h0, -⟩
    · exfalso
      obtain ⟨q, hqY, hq⟩ := hy1
      have hle : Y ⊓ F = Y := eq_of_le_of_rk_le hQ inf_le_left (by rw [hj, hc, h])
      have : q ∈ Y ⊓ F := by rw [hle]; exact hqY
      exact hq ((mem_fixed_zpowers_iff (b := y)).1 this.2)
    · rwa [h0, zero_mul, rk_eq_zero_iff hQ] at hj
  obtain ⟨c, j, hc, hj, -, hc4, hcj⟩ := key S hSY hSΛ hSy
  rcases hcj with h | ⟨-, h4⟩
  · left
    have hSF : S ⊓ F = S := eq_of_le_of_rk_le hQ inf_le_left (by rw [hj, hc, h])
    rw [eq_bot_iff]
    intro s hs
    have hs' : s ∈ S ⊓ F := by rw [hSF]; exact hs
    have : s ∈ Y ⊓ F := ⟨hSY hs, hs'.2⟩
    rwa [hYF] at this
  · right
    exact eq_of_le_of_rk_le hQ hSY (by rw [hc, hY.2.2, h4])


end Orbit

section SecCount

variable {W : Type} [CommGroup W]

@[expose] def secFix (A : Subgroup (MulAut W)) (H H' : Subgroup W) : Subgroup W where
  carrier := {w | w ∈ H ∧ ∀ a ∈ A, a w * w⁻¹ ∈ H'}
  one_mem' := ⟨H.one_mem, fun a _ => by simp⟩
  mul_mem' := fun {x y} hx hy =>
    ⟨H.mul_mem hx.1 hy.1, fun a ha => by
      have h : a (x * y) * (x * y)⁻¹ = (a x * x⁻¹) * (a y * y⁻¹) := by
        rw [map_mul, mul_inv_rev]
        ac_rfl
      rw [h]
      exact H'.mul_mem (hx.2 a ha) (hy.2 a ha)⟩
  inv_mem' := fun {x} hx =>
    ⟨H.inv_mem hx.1, fun a ha => by
      have h : a x⁻¹ * (x⁻¹)⁻¹ = (a x * x⁻¹)⁻¹ := by
        rw [map_inv, inv_inv, mul_inv_rev, inv_inv]
        exact mul_comm _ _
      rw [h]
      exact H'.inv_mem (hx.2 a ha)⟩

theorem mem_secFix {A : Subgroup (MulAut W)} {H H' : Subgroup W} {w : W} :
    w ∈ secFix A H H' ↔ w ∈ H ∧ ∀ a ∈ A, a w * w⁻¹ ∈ H' := Iff.rfl

theorem secFix_le (A : Subgroup (MulAut W)) (H H' : Subgroup W) : secFix A H H' ≤ H :=
  fun _ h => h.1

@[expose] noncomputable def nSec (A : Subgroup (MulAut W)) (H H' : Subgroup W) : ℕ :=
  rk ↥H - rk ↥(secFix A H H')

theorem nSec_add_le [Finite W] (A : Subgroup (MulAut W)) {H H' H'' : Subgroup W}
    (h1 : H'' ≤ H') (h2 : H' ≤ H) (hA : ∀ a ∈ A, ∀ w ∈ H', a w ∈ H') :
    nSec A H H' + nSec A H' H'' ≤ nSec A H H'' := by
  unfold nSec
  set F := secFix A H H'' with hF
  set F' := secFix A H H' with hF'
  set F₂ := secFix A H' H'' with hF₂
  have hinf : F ⊓ H' = F₂ := by
    ext w
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h2 h.1, h.2⟩, h.1⟩⟩
  have hsup : F ⊔ H' ≤ F' := by
    refine sup_le (fun w hw => ⟨hw.1, fun a ha => h1 (hw.2 a ha)⟩) fun w hw => ⟨h2 hw, ?_⟩
    exact fun a ha => H'.mul_mem (hA a ha w hw) (H'.inv_mem hw)
  have e1 := rk_sup_add_rk_inf F H'
  rw [hinf] at e1
  have e2 := rk_mono hsup
  have e3 : rk ↥F' ≤ rk ↥H := rk_mono (secFix_le A H H')
  have e4 : rk ↥F₂ ≤ rk ↥H' := rk_mono (secFix_le A H' H'')
  have e5 : rk ↥H' ≤ rk ↥H := rk_mono h2
  omega

theorem one_le_nSec [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)}
    {H H' : Subgroup W} {a : MulAut W} (ha : a ∈ A) {w : W} (hw : w ∈ H) (haw : a w * w⁻¹ ∉ H') :
    1 ≤ nSec A H H' := by
  unfold nSec
  have hlt : secFix A H H' < H := by
    refine lt_of_le_of_ne (secFix_le A H H') fun h => haw ?_
    have hw' : w ∈ secFix A H H' := by rw [h]; exact hw
    exact hw'.2 a ha
  have := rk_mono (secFix_le A H H')
  have hne : rk ↥(secFix A H H') ≠ rk ↥H := fun h =>
    hlt.ne (eq_of_le_of_rk_le hW (secFix_le A H H') h.ge)
  omega

theorem secFix_bot (A : Subgroup (MulAut W)) (H : Subgroup W) :
    secFix A H ⊥ = H ⊓ fixV A := by
  ext w
  simp only [mem_secFix, Subgroup.mem_bot, mul_inv_eq_one, Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.1, fun a ha => h.2 a ha⟩, fun h => ⟨h.1, fun a ha => h.2 a ha⟩⟩

end SecCount


section Split

theorem quot_sq_of {W : Type} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1) (N : Subgroup W) :
    ∀ q : W ⧸ N, q ^ 2 = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H v => rw [← QuotientGroup.mk_pow, hW v, QuotientGroup.mk_one]

variable {W : Type} [CommGroup W] [Finite W] {M Mp L : Subgroup (MulAut W)}

omit [Finite W] in
theorem smul_mem_commV_of_comm {L : Subgroup (MulAut W)} {y : MulAut W}
    (hyL : ∀ l ∈ L, y * l = l * y) : ∀ u ∈ commV L, y u ∈ commV L := by
  refine B15P4.map_commV_mem (Subgroup.mem_normalizer_iff.2 fun x => ?_)
  constructor
  · intro hx
    rw [hyL x hx, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  · intro hx
    have h1 : x = y⁻¹ * (y * x * y⁻¹) * y := by group
    have h2 : y⁻¹ * (y * x * y⁻¹) * y = y * x * y⁻¹ := by
      rw [mul_assoc, ← hyL _ hx, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1, h2]
    exact hx

theorem inf_fixV_eq_bot_of_split (hW : ∀ w : W, w ^ 2 = 1)
    (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))) (hLMp : L ≤ Mp)
    (hLperf : ⁅L, L⁆ = L) (hUZ : commV L ⊓ fixV Mp = commV L ⊓ fixV L)
    {I : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))}
    (hI : letI := qAct hMp; XMod.IsIrr ↥(L.subgroupOf M) I) (hIodd : Odd (rk ↥I))
    (hY : letI := qAct hMp; IsotypicOfLength ↥(L.subgroupOf M) (tilde Mp ⊤ (commV L)) I 4)
    {y : MulAut W} (hyM : y ∈ M) (hyL : ∀ l ∈ L, y * l = l * y)
    (hy5 : letI := qAct hMp; ∀ q ∈ tilde Mp ⊤ (commV L), (⟨y, hyM⟩ : ↥M) ^ 5 • q = q)
    (hy1 : letI := qAct hMp; ∃ q ∈ tilde Mp ⊤ (commV L), (⟨y, hyM⟩ : ↥M) • q ≠ q)
    {P : Subgroup W} (hPU : P ≤ commV L) (hP : XMod.IsIrr ↥L P) (hPZ : P ⊓ fixV Mp = ⊥) :
    commV L ⊓ fixV Mp = ⊥ := by
  let _i := qAct hMp
  set U := commV L with hU
  set κ := QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) with hκ
  have hker : ∀ w : W, κ w = 1 ↔ w ∈ fixV Mp := by
    intro w
    rw [hκ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq]
  have hZL : fixV Mp ≤ fixV L := fun w hw => mem_fixV.2 fun x hx => mem_fixV.1 hw x (hLMp hx)
  have hgMp : ∀ g ∈ M, ∀ w ∈ fixV Mp, g w ∈ fixV Mp := by
    intro g hg w hw
    refine mem_fixV.2 fun x hx => ?_
    have hx' : g⁻¹ * x * g ∈ Mp := (Subgroup.mem_normalizer_iff''.1 (hMp hg) x).1 hx
    have h1 : (g⁻¹ * x * g) w = w := mem_fixV.1 hw _ hx'
    calc x (g w) = g ((g⁻¹ * x * g) w) := by simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      _ = g w := by rw [h1]
  have hyU : ∀ u ∈ U, y u ∈ U := smul_mem_commV_of_comm hyL
  let Pc := {P' : Subgroup W // P' ≤ U ∧ XMod.IsIrr ↥L P' ∧ P' ⊓ fixV Mp = ⊥}
  set X : Subgroup W := ⨆ P' : Pc, (P' : Subgroup W) with hX
  have hXU : X ≤ U := iSup_le fun P' => P'.2.1
  have hXL : XMod.IsInv ↥L X := XMod.isInv_iSup fun P' => P'.2.2.1.1
  have hPX : P ≤ X := le_iSup (fun P' : Pc => (P' : Subgroup W)) ⟨P, hPU, hP, hPZ⟩
  have hymem : ∀ P' : Pc, y • (P' : Subgroup W) ≤ X := by
    intro P'
    refine le_iSup (fun P' : Pc => (P' : Subgroup W)) ⟨y • (P' : Subgroup W), ?_, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hyU w (P'.2.1 hw)
    · exact isIrr_smul_of_comm P'.2.2.1 hyL
    · rw [eq_bot_iff]
      rintro _ ⟨⟨w, hw, rfl⟩, hwZ⟩
      have hw' : w ∈ fixV Mp := by
        have h1 := hgMp y⁻¹ (M.inv_mem hyM) _ hwZ
        change y⁻¹ (y w) ∈ fixV Mp at h1
        rwa [MulAut.inv_apply_self] at h1
      have : w ∈ (P' : Subgroup W) ⊓ fixV Mp := ⟨hw, hw'⟩
      rw [P'.2.2.2, Subgroup.mem_bot] at this
      change y w ∈ (⊥ : Subgroup W)
      rw [this, map_one]
      exact Subgroup.one_mem _
  have hXy : ∀ w ∈ X, y w ∈ X := by
    intro w hw
    refine Subgroup.iSup_induction (fun P' : Pc => (P' : Subgroup W)) (C := fun x => y x ∈ X) hw
      (fun P' x hx => hymem P' ⟨x, hx, rfl⟩) (by rw [map_one]; exact X.one_mem) ?_
    intro x x' hx hx'
    rw [map_mul]
    exact X.mul_mem hx hx'
  have hXfix : X ⊓ fixV L = ⊥ := by
    by_contra hne
    have hinv : XMod.IsInv ↥L (X ⊓ fixV L) :=
      hXL.inf fun l w hw => by
        have h1 : (l : MulAut W) w = w := mem_fixV.1 hw l l.2
        change (l : MulAut W) w ∈ fixV L
        rw [h1]
        exact hw
    obtain ⟨R, hRle, hR⟩ := exists_isIrr_le (Λ := L) hinv hne
    obtain ⟨P', hiso⟩ := exists_iso_of_le_iSup (S := fun P' : Pc => (P' : Subgroup W))
      (fun P' => P'.2.2.1) hR (hRle.trans inf_le_left)
    obtain ⟨φ, hφ⟩ := hiso
    have hP'fix : (P' : Subgroup W) ≤ fixV L := by
      intro p hp
      obtain ⟨r, hr⟩ := φ.surjective ⟨p, hp⟩
      refine mem_fixV.2 fun l hl => ?_
      have hr1 : (⟨l, hl⟩ : ↥L) • (r : W) = (r : W) := mem_fixV.1 (hRle r.2).2 l hl
      have h2 := hφ ⟨l, hl⟩ r r hr1
      rw [hr] at h2
      exact h2
    have hbot : (P' : Subgroup W) = ⊥ := by
      rw [← inf_eq_left.2 hP'fix, ← inf_eq_left.2 P'.2.1, inf_assoc, ← hUZ, ← inf_assoc,
        inf_eq_left.2 P'.2.1, P'.2.2.2]
    exact P'.2.2.1.2.1.ne' hbot
  set Xt := X.map κ with hXt
  have hXtY : Xt ≤ tilde Mp ⊤ U := Subgroup.map_mono hXU
  have hXtΛ : XMod.IsInv ↥(L.subgroupOf M) Xt := by
    rintro l _ ⟨w, hw, rfl⟩
    exact ⟨_, hXL ⟨(l : MulAut W), Subgroup.mem_subgroupOf.1 l.2⟩ w hw, rfl⟩
  have hXty : ∀ q ∈ Xt, (⟨y, hyM⟩ : ↥M) • q ∈ Xt := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, hXy w hw, rfl⟩
  have hXtne : Xt ≠ ⊥ := by
    intro h0
    obtain ⟨p, hp1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hP.2.1.ne'
    have h1 : κ (p : W) ∈ Xt := ⟨p, hPX p.2, rfl⟩
    rw [h0, Subgroup.mem_bot, hker] at h1
    have : (p : W) ∈ P ⊓ fixV Mp := ⟨p.2, h1⟩
    rw [hPZ, Subgroup.mem_bot] at this
    exact hp1 (Subtype.ext this)
  have hyΛ : ∀ l ∈ L.subgroupOf M, (⟨y, hyM⟩ : ↥M) * l = l * ⟨y, hyM⟩ := fun l hl =>
    Subtype.ext (hyL _ (Subgroup.mem_subgroupOf.1 hl))
  have hyY : ∀ q ∈ tilde Mp ⊤ U, (⟨y, hyM⟩ : ↥M) • q ∈ tilde Mp ⊤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨_, hyU u hu, rfl⟩
  have hXtQ : Xt = tilde Mp ⊤ U := by
    rcases eq_bot_or_eq_of_pow_five (quot_sq_of hW _) hI hIodd hY hyΛ hy5 hyY hy1 hXtY hXtΛ
      hXty with h | h
    · exact absurd h hXtne
    · exact h
  have hUle : U ≤ X ⊔ U ⊓ fixV Mp := by
    intro u hu
    have h1 : κ u ∈ Xt := by rw [hXtQ]; exact ⟨u, hu, rfl⟩
    obtain ⟨x, hx, hxu⟩ := h1
    have hz : x⁻¹ * u ∈ U ⊓ fixV Mp := by
      refine ⟨U.mul_mem (U.inv_mem (hXU hx)) hu, (hker _).1 ?_⟩
      rw [map_mul, map_inv, hxu, inv_mul_cancel]
    have : u = x * (x⁻¹ * u) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hx hz
  have hUX : U ≤ X := by
    have h1 : commSub U L = U := B15P4.commSub_commV_of_perfect hLperf
    rw [← h1]
    refine (commSub_mono hUle le_rfl).trans ?_
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup.1 hw
    have hxz : x z = z := mem_fixV.1 (hZL hz.2) x hx
    have e : x (a * z) * (a * z)⁻¹ = x a * a⁻¹ := by
      rw [map_mul, hxz]
      group
    rw [e]
    exact X.mul_mem (hXL ⟨x, hx⟩ a ha) (X.inv_mem ha)
  have hZX : U ⊓ fixV Mp ≤ X ⊓ fixV L := fun z hz => ⟨hUX hz.1, hZL hz.2⟩
  rw [hXfix] at hZX
  exact le_bot_iff.1 hZX

end Split

section Cover

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem comm_of_trivial_on {X : Subgroup (MulAut W)} {P : Subgroup W} {a : MulAut W}
    (haX : a ∈ Subgroup.normalizer (X : Set (MulAut W))) (hXP : ∀ x ∈ X, ∀ v ∈ P, x v ∈ P)
    (hfaith : ∀ x ∈ X, (∀ v ∈ P, x v = v) → x = 1) (ha : ∀ v ∈ P, a v = v)
    (haP : ∀ v ∈ P, a⁻¹ v ∈ P) : ∀ x ∈ X, a * x = x * a := by
  intro x hx
  have hc : a * x * a⁻¹ * x⁻¹ ∈ X :=
    X.mul_mem ((Subgroup.mem_normalizer_iff.1 haX x).1 hx) (X.inv_mem hx)
  have h1 : a * x * a⁻¹ * x⁻¹ = 1 := by
    refine hfaith _ hc fun v hv => ?_
    have hv1 : x⁻¹ v ∈ P := hXP _ (X.inv_mem hx) v hv
    have hv2 : a⁻¹ (x⁻¹ v) = x⁻¹ v := by
      have := ha _ (haP _ hv1)
      rw [MulAut.apply_inv_self] at this
      exact this.symm
    have hv3 : x (x⁻¹ v) = v := by simp
    simp only [MulAut.mul_apply]
    rw [hv2, hv3, ha v hv]
  calc a * x = a * x * a⁻¹ * x⁻¹ * (x * a) := by group
    _ = x * a := by rw [h1, one_mul]

theorem two_le_nSec_cover (hW : ∀ w : W, w ^ 2 = 1) {X A : Subgroup (MulAut W)}
    {P : Subgroup W} (hXP : ∀ x ∈ X, ∀ v ∈ P, x v ∈ P) (hcomm : XMod.commOf ↥X P = P)
    (hnat : BinaryNaturalSL X P (P ⊓ fixV X) 3 1) (hZ : Nat.card ↥(P ⊓ fixV X) = 2)
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hAP : ∀ a ∈ A, ∀ v, a v ∈ P ↔ v ∈ P) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAC : ¬ ∀ a ∈ A, ∀ x ∈ X, a * x = x * a) : 2 ≤ nSec A P ⊥ := by
  push Not at hAC
  obtain ⟨a, ha, x₀, hx₀, hax⟩ := hAC
  have hfaith := cover_faithful hW X P hXP hcomm hnat hZ
  obtain ⟨l, hl, hal⟩ := cover_normalizer_stab hW X P hXP hcomm hnat hZ a
    (fun x => Subgroup.mem_normalizer_iff.1 (hAX ha) x) (hAP a ha)
  have haP : ∀ v ∈ P, a⁻¹ v ∈ P := fun v hv => (hAP a ha _).1 (by rwa [MulAut.apply_inv_self])
  have hl1 : l ≠ 1 := by
    rintro rfl
    exact hax (comm_of_trivial_on (hAX ha) hXP hfaith (fun v hv => by rw [hal v hv]; rfl) haP
      x₀ hx₀)
  have hl2 : l ^ 2 = 1 := by
    refine hfaith _ (X.pow_mem hl 2) fun v hv => ?_
    have h1 : (a ^ 2) v = v := by rw [hA2 a ha]; rfl
    rw [pow_two, MulAut.mul_apply] at h1 ⊢
    rw [← hal v hv, ← hal _ ((hAP a ha v).2 hv)]
    exact h1
  obtain ⟨hc4, hceq⟩ := cover_commSub_involution hW X P hXP hcomm hnat hZ l hl hl1 hl2
  have hfix4 : Nat.card ↥(P ⊓ fixV (Subgroup.zpowers l)) = 4 := by rw [← hceq, hc4]
  have hrk2 : rk ↥(P ⊓ fixV (Subgroup.zpowers l)) = 2 := by
    rw [card_eq_two_pow hW] at hfix4
    exact Nat.pow_right_injective le_rfl (hfix4.trans (by norm_num : (4 : ℕ) = 2 ^ 2))
  have hle : secFix A P ⊥ ≤ P ⊓ fixV (Subgroup.zpowers l) := by
    rw [secFix_bot]
    rintro v ⟨hv, hvA⟩
    refine ⟨hv, mem_fixV.2 fun g hg => ?_⟩
    have hlv : l v = v := by rw [← hal v hv]; exact mem_fixV.1 hvA a ha
    have hst : l ∈ MulAction.stabilizer (MulAut W) v := by
      rw [MulAction.mem_stabilizer_iff]
      exact hlv
    have h1 := Subgroup.zpowers_le.2 hst hg
    rw [MulAction.mem_stabilizer_iff] at h1
    exact h1
  have hP16 : rk ↥P = 4 := by
    obtain ⟨K, _, _, hK, π, hπ⟩ := hnat
    have h1 := G64.RealizesVia.card_eq hπ
    rw [G64.card_natMod, hK, hZ, card_eq_two_pow hW] at h1
    exact Nat.pow_right_injective le_rfl (h1.trans (by norm_num : ((2 : ℕ) ^ 1) ^ 3 * 2 = 2 ^ 4))
  have := rk_mono hle
  unfold nSec
  omega

end Cover

section CoverRank

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem card_le_four_of_equiv {X : Subgroup (MulAut W)} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 1) (e : ↥(StatedSL 3 K) ≃* ↥X) {E : Subgroup ↥X}
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card ↥E ≤ 4 := by
  have h2 : (2 : K) = 0 := by
    have := charP_two_of_card hK
    exact CharTwo.two_eq_zero
  let f : ↥E → Matrix (Fin 3) (Fin 3) K := fun x =>
    (((e.symm (x : ↥X) : ↥(StatedSL 3 K)) : Matrix.GeneralLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    exact Units.ext hxy
  have hfmul : ∀ x y : ↥E, f x * f y = f (x * y) := by
    intro x y
    simp only [f, Subgroup.coe_mul, map_mul, Units.val_mul]
  set S : Set (Matrix (Fin 3) (Fin 3) K) := Set.range f with hS
  have hS2 : ∀ g ∈ S, g * g = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [hfmul]
    have : x * x = 1 := by
      have h := hE2 x x.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, ← pow_two, h]
      rfl
    rw [this]
    simp [f]
  have hSc : ∀ g ∈ S, ∀ h ∈ S, g * h = h * g := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hfmul, hfmul]
    congr 1
    exact Subtype.ext (hEc x x.2 y y.2)
  have h1 := SmithD310U.card_le_sq h2 hS2 hSc
  rw [hK] at h1
  have h3 : Nat.card ↥E = Nat.card S := by
    rw [hS, Nat.card_range_of_injective hf]
  rw [h3]
  simpa using h1

theorem rk_le_add_two_of_cover (hW : ∀ w : W, w ^ 2 = 1) {X A : Subgroup (MulAut W)}
    {P : Subgroup W} (hXP : ∀ x ∈ X, ∀ v ∈ P, x v ∈ P) (hcomm : XMod.commOf ↥X P = P)
    (hnat : BinaryNaturalSL X P (P ⊓ fixV X) 3 1) (hZ : Nat.card ↥(P ⊓ fixV X) = 2)
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hAP : ∀ a ∈ A, ∀ v, a v ∈ P ↔ v ∈ P) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    rk ↥A ≤ rk ↥(A ⊓ Subgroup.centralizer (X : Set (MulAut W))) + 2 := by
  have hfaith := cover_faithful hW X P hXP hcomm hnat hZ
  have huniq : ∀ l ∈ X, ∀ l' ∈ X, (∀ v ∈ P, l v = l' v) → l = l' := by
    intro l hl l' hl' h
    have h1 := hfaith (l'⁻¹ * l) (X.mul_mem (X.inv_mem hl') hl) fun v hv => by
      rw [MulAut.mul_apply, h v hv, MulAut.inv_apply_self]
    rw [mul_eq_one_iff_eq_inv] at h1
    exact (inv_injective h1).symm
  have hst : ∀ a : ↥A, ∃ l : ↥X, ∀ v ∈ P, (a : MulAut W) v = (l : MulAut W) v := by
    intro a
    obtain ⟨l, hl, hal⟩ := cover_normalizer_stab hW X P hXP hcomm hnat hZ a
      (fun x => Subgroup.mem_normalizer_iff.1 (hAX a.2) x) (hAP a a.2)
    exact ⟨⟨l, hl⟩, hal⟩
  choose ℓ hℓ using hst
  have hℓone : ℓ 1 = 1 := Subtype.ext (huniq _ (ℓ 1).2 _ X.one_mem fun v hv => by
    rw [← hℓ 1 v hv]; rfl)
  have hℓmul : ∀ a b : ↥A, ℓ (a * b) = ℓ a * ℓ b := by
    intro a b
    refine Subtype.ext (huniq _ (ℓ (a * b)).2 _ (ℓ a * ℓ b).2 fun v hv => ?_)
    rw [← hℓ (a * b) v hv, Subgroup.coe_mul, Subgroup.coe_mul, MulAut.mul_apply,
      MulAut.mul_apply, ← hℓ b v hv, ← hℓ a _ ((hAP b b.2 v).2 hv)]
  let φ : ↥A →* ↥X := { toFun := ℓ, map_one' := hℓone, map_mul' := hℓmul }
  have hker : φ.ker ≤ (A ⊓ Subgroup.centralizer (X : Set (MulAut W))).subgroupOf A := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    have htriv : ∀ v ∈ P, (a : MulAut W) v = v := fun v hv => by
      rw [hℓ a v hv]
      show ((φ a : ↥X) : MulAut W) v = v
      rw [ha]
      rfl
    have haP : ∀ v ∈ P, (a : MulAut W)⁻¹ v ∈ P := fun v hv =>
      (hAP a a.2 _).1 (by rwa [MulAut.apply_inv_self])
    refine Subgroup.mem_subgroupOf.2 ⟨a.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    exact (comm_of_trivial_on (hAX a.2) hXP hfaith htriv haP x hx).symm
  obtain ⟨K, _, _, hK, e, -⟩ := exists_equiv_of_binaryNaturalSL hnat
  have hrange : Nat.card ↥φ.range ≤ 4 := by
    refine card_le_four_of_equiv hK e ?_ ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAc a a.2 b b.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hA2 a a.2]; rfl)
      rw [this, map_one]
  have hcard : Nat.card ↥A = Nat.card ↥φ.ker * Nat.card ↥φ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
  have hrP : IsPGroup 2 ↥φ.range := by
    rintro ⟨_, a, rfl⟩
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have : a ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hA2 a a.2]; rfl)
    show ((φ a ^ 2 : ↥X) : MulAut W) = 1
    rw [← map_pow, this, map_one]
    rfl
  have hrr : rk ↥φ.range ≤ 2 := by
    have h1 := card_eq_two_pow_of_isPGroup hrP
    rw [h1] at hrange
    by_contra hc
    push Not at hc
    have : 2 ^ 3 ≤ 2 ^ rk ↥φ.range := Nat.pow_le_pow_right (by norm_num) hc
    omega
  have hkr : rk ↥φ.ker ≤ rk ↥(A ⊓ Subgroup.centralizer (X : Set (MulAut W))) := by
    have h1 := rk_mono hker
    have h2 : rk ↥((A ⊓ Subgroup.centralizer (X : Set (MulAut W))).subgroupOf A) =
        rk ↥(A ⊓ Subgroup.centralizer (X : Set (MulAut W))) := by
      unfold rk
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    omega
  have hrkA : rk ↥A = rk ↥φ.ker + rk ↥φ.range := by
    unfold rk
    rw [hcard, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne']
  omega

end CoverRank

section Chain

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem comm_or_exists_moved {Λ A : Subgroup Γ} (hΛs : IsSimpleGroup ↥Λ)
    (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ) {J J' : Subgroup Q} (hJJ' : J < J')
    (hJΛ : XMod.IsInv ↥Λ J) (hJ'Λ : XMod.IsInv ↥Λ J') (hJA : ∀ a ∈ A, ∀ q ∈ J, a • q ∈ J)
    (hcomm : XMod.commOf ↥Λ J' = J') :
    (∀ a ∈ A, ∀ l ∈ Λ, a * l = l * a) ∨ ∃ a ∈ A, ∃ q ∈ J', a • q * q⁻¹ ∉ J := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a₀, ha₀, l₀, hl₀, hne⟩, htriv⟩ := hcon
  let N : Subgroup ↥Λ :=
    { carrier := {x | ∀ q ∈ J', (x : Γ) • q * q⁻¹ ∈ J}
      one_mem' := fun q _ => by simp [J.one_mem]
      mul_mem' := fun {x y} hx hy q hq => by
        have h1 := hx _ (hJ'Λ y q hq)
        have h2 := hy q hq
        have e : ((x * y : ↥Λ) : Γ) • q * q⁻¹ = ((x : Γ) • (y : Γ) • q * ((y : Γ) • q)⁻¹) *
            ((y : Γ) • q * q⁻¹) := by
          rw [Subgroup.coe_mul, mul_smul]
          group
        rw [e]
        exact J.mul_mem h1 h2
      inv_mem' := fun {x} hx q hq => by
        have hq' : (x⁻¹ : ↥Λ) • q ∈ J' := hJ'Λ _ q hq
        have h1 : (x : Γ) • ((x : Γ)⁻¹ • q) * ((x : Γ)⁻¹ • q)⁻¹ ∈ J := hx _ hq'
        rw [smul_inv_smul] at h1
        show (x : Γ)⁻¹ • q * q⁻¹ ∈ J
        have e : (x : Γ)⁻¹ • q * q⁻¹ = (q * ((x : Γ)⁻¹ • q)⁻¹)⁻¹ := by group
        rw [e]
        exact J.inv_mem h1 }
  have hNn : N.Normal := by
    refine ⟨fun x hx g q hq => ?_⟩
    have hq' : (g⁻¹ : ↥Λ) • q ∈ J' := hJ'Λ _ q hq
    have h1 := hx _ hq'
    have h2 := hJΛ g _ h1
    have e : ((g * x * g⁻¹ : ↥Λ) : Γ) • q * q⁻¹ =
        g • ((x : Γ) • ((g⁻¹ : ↥Λ) • q) * ((g⁻¹ : ↥Λ) • q)⁻¹) := by
      rw [smul_mul', smul_inv', Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul]
      show _ = (g : Γ) • (x : Γ) • ((g⁻¹ : ↥Λ) : Γ) • q * ((g : Γ) • ((g⁻¹ : ↥Λ) : Γ) • q)⁻¹
      rw [Subgroup.coe_inv, smul_inv_smul]
    rw [e]
    exact h2
  rcases hΛs.eq_bot_or_eq_top_of_normal N with hN | hN
  ·
    apply hne
    have hc : a₀ * l₀ * a₀⁻¹ * l₀⁻¹ ∈ Λ := Λ.mul_mem (hAΛ a₀ ha₀ l₀ hl₀) (Λ.inv_mem hl₀)
    have hmem : (⟨_, hc⟩ : ↥Λ) ∈ N := by
      intro q hq
      set q₁ := l₀⁻¹ • q with hq₁
      have hq₁J' : q₁ ∈ J' := hJ'Λ ⟨l₀⁻¹, Λ.inv_mem hl₀⟩ q hq
      set j₁ := a₀⁻¹ • q₁ * q₁⁻¹ with hj₁
      have hj₁J : j₁ ∈ J := htriv _ (A.inv_mem ha₀) q₁ hq₁J'
      have hlj : l₀ • j₁ ∈ J := hJΛ ⟨l₀, hl₀⟩ j₁ hj₁J
      have halj : a₀ • (l₀ • j₁) ∈ J := hJA a₀ ha₀ _ hlj
      have haq : a₀ • q * q⁻¹ ∈ J := htriv a₀ ha₀ q hq
      have e1 : a₀⁻¹ • q₁ = j₁ * q₁ := by rw [hj₁]; group
      have e2 : l₀ • q₁ = q := by rw [hq₁, smul_inv_smul]
      have e : (a₀ * l₀ * a₀⁻¹ * l₀⁻¹) • q * q⁻¹ = a₀ • (l₀ • j₁) * (a₀ • q * q⁻¹) := by
        rw [mul_smul, mul_smul, mul_smul, ← hq₁, e1, smul_mul', e2, smul_mul']
        group
      show (a₀ * l₀ * a₀⁻¹ * l₀⁻¹) • q * q⁻¹ ∈ J
      rw [e]
      exact J.mul_mem halj haq
    rw [hN, Subgroup.mem_bot] at hmem
    have h1 : a₀ * l₀ * a₀⁻¹ * l₀⁻¹ = 1 := congrArg Subtype.val hmem
    calc a₀ * l₀ = a₀ * l₀ * a₀⁻¹ * l₀⁻¹ * (l₀ * a₀) := by group
      _ = l₀ * a₀ := by rw [h1, one_mul]
  ·
    apply hJJ'.not_ge
    rw [← hcomm, XMod.commOf_le_iff]
    intro x q hq
    have hx : x ∈ N := by rw [hN]; trivial
    exact hx q hq

end Chain

section ChainFour

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem exists_chain_four [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ A : Subgroup Γ}
    {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) (hY : IsotypicOfLength ↥Λ Y I 4)
    (hA2 : IsPGroup 2 ↥A) (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ)
    (hAY : ∀ a ∈ A, ∀ q ∈ Y, a • q ∈ Y) :
    ∃ Y₁ Y₂ Y₃ : Subgroup Q, XMod.IsIrr ↥Λ Y₁ ∧ XMod.IsIrrSec ↥Λ Y₁ Y₂ ∧
      XMod.IsIrrSec ↥Λ Y₂ Y₃ ∧ XMod.IsIrrSec ↥Λ Y₃ Y ∧ XMod.IsInv ↥Λ Y₂ ∧
      XMod.IsInv ↥Λ Y₃ ∧ (∀ a ∈ A, ∀ q ∈ Y₁, a • q ∈ Y₁) ∧ (∀ a ∈ A, ∀ q ∈ Y₂, a • q ∈ Y₂) ∧
      (∀ a ∈ A, ∀ q ∈ Y₃, a • q ∈ Y₃) := by
  obtain ⟨Y₃, hY₃Y, hY₃i, hY₃m, hY₃A⟩ := exists_max_fixed hQ hI hY (by norm_num) hA2 hAΛ hAY
  have hY₃ : IsotypicOfLength ↥Λ Y₃ I 3 := isotypicOfLength_of_max hQ hI hY hY₃Y hY₃i hY₃m
  obtain ⟨Y₂, hY₂Y, hY₂i, hY₂m, hY₂A⟩ := exists_max_fixed hQ hI hY₃ (by norm_num) hA2 hAΛ hY₃A
  have hY₂ : IsotypicOfLength ↥Λ Y₂ I 2 := isotypicOfLength_of_max hQ hI hY₃ hY₂Y hY₂i hY₂m
  obtain ⟨Y₁, hY₁Y, hY₁i, hY₁m, hY₁A⟩ := exists_max_fixed hQ hI hY₂ (by norm_num) hA2 hAΛ hY₂A
  have hY₁ : IsotypicOfLength ↥Λ Y₁ I 1 := isotypicOfLength_of_max hQ hI hY₂ hY₁Y hY₁i hY₁m
  obtain ⟨Y₀, hY₀Y, hY₀i, hY₀m, -⟩ := exists_max_fixed hQ hI hY₁ (by norm_num) hA2 hAΛ hY₁A
  have hY₀ : IsotypicOfLength ↥Λ Y₀ I 0 := isotypicOfLength_of_max hQ hI hY₁ hY₀Y hY₀i hY₀m
  have hY₀b : Y₀ = ⊥ := (rk_eq_zero_iff hQ).1 (by rw [hY₀.2.2, zero_mul])
  rw [hY₀b] at hY₀m
  exact ⟨Y₁, Y₂, Y₃, ⟨hY₁i, hY₀m⟩, hY₁m, hY₂m, hY₃m, hY₂i, hY₃i, hY₁A, hY₂A, hY₃A⟩

end ChainFour

section Lift

variable {W : Type} [CommGroup W] [Finite W] {M Mp : Subgroup (MulAut W)}

omit [Finite W] in
theorem commSub_isInv (D : Subgroup W) (K : Subgroup (MulAut W)) :
    ∀ x ∈ K, ∀ w ∈ commSub D K, x w ∈ commSub D K := by
  intro x hx w hw
  unfold commSub at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨y, hy, v, hv, rfl⟩ := hc
    have e : x (y v * v⁻¹) = ((x * y) v * v⁻¹) * (x v * v⁻¹)⁻¹ := by
      simp only [map_mul, map_inv, MulAut.mul_apply]
      group
    rw [e]
    exact mul_mem (Subgroup.subset_closure ⟨x * y, K.mul_mem hx hy, v, hv, rfl⟩)
      (inv_mem (Subgroup.subset_closure ⟨x, hx, v, hv, rfl⟩))
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

omit [Finite W] in
theorem commSub_stab {D : Subgroup W} {K : Subgroup (MulAut W)} {g : MulAut W}
    (hgK : g ∈ Subgroup.normalizer (K : Set (MulAut W))) (hgD : ∀ v ∈ D, g v ∈ D) :
    ∀ w ∈ commSub D K, g w ∈ commSub D K := by
  intro w hw
  unfold commSub at hw ⊢
  induction hw using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨y, hy, v, hv, rfl⟩ := hc
    have e : g (y v * v⁻¹) = (g * y * g⁻¹) (g v) * (g v)⁻¹ := by
      simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [e]
    exact Subgroup.subset_closure ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.1 hgK y).1 hy,
      g v, hgD v hv, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

omit [Finite W] in
theorem tilde_commSub (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    {X : Subgroup (MulAut W)}
    (hXM : X ≤ M) (D : Subgroup W) :
    letI := qAct hMp
    tilde Mp ⊤ (commSub D X) = XMod.commOf ↥(X.subgroupOf M) (tilde Mp ⊤ D) := by
  let _i := qAct hMp
  unfold tilde commSub XMod.commOf
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, ⟨x, hx, v, hv, rfl⟩, rfl⟩
    refine ⟨⟨⟨x, hXM hx⟩, Subgroup.mem_subgroupOf.2 hx⟩, _, ⟨v, hv, rfl⟩, ?_⟩
    rw [map_mul, map_inv]
    rfl
  · rintro ⟨l, _, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨_, ⟨((l : ↥M) : MulAut W), Subgroup.mem_subgroupOf.1 l.2, v, hv, rfl⟩, ?_⟩
    rw [map_mul, map_inv]
    rfl

end Lift

section Lift2

variable {W : Type} [CommGroup W] [Finite W] {M Mp : Subgroup (MulAut W)}

omit [Finite W] in
theorem isIrr_of_tilde (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    {X : Subgroup (MulAut W)} {P : Subgroup W} (hPX : ∀ x ∈ X, ∀ v ∈ P, x v ∈ P)
    (hPZ : P ⊓ fixV Mp = ⊥)
    (hirr : letI := qAct hMp; XMod.IsIrr ↥(X.subgroupOf M) (tilde Mp ⊤ P)) :
    XMod.IsIrr ↥X P := by
  let _i := qAct hMp
  set κ := QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) with hκ
  have hker : ∀ w : W, κ w = 1 ↔ w ∈ fixV Mp := by
    intro w
    rw [hκ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq]
  refine ⟨fun x v hv => hPX x x.2 v hv, bot_lt_iff_ne_bot.2 fun h => ?_, fun J hJ _ hJP => ?_⟩
  · apply hirr.2.1.ne'
    rw [h]
    exact Subgroup.map_bot _
  · have hJt : XMod.IsInv ↥(X.subgroupOf M) (tilde Mp ⊤ J) := by
      rintro l _ ⟨w, hw, rfl⟩
      exact ⟨_, hJ ⟨((l : ↥M) : MulAut W), Subgroup.mem_subgroupOf.1 l.2⟩ w hw, rfl⟩
    rcases hirr.2.2 _ hJt bot_le (Subgroup.map_mono hJP) with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      have h1 : κ w ∈ tilde Mp ⊤ J := ⟨w, hw, rfl⟩
      rw [h, Subgroup.mem_bot, hker] at h1
      have : w ∈ P ⊓ fixV Mp := ⟨hJP hw, h1⟩
      rwa [hPZ] at this
    · right
      refine le_antisymm hJP fun w hw => ?_
      have h1 : κ w ∈ tilde Mp ⊤ J := by rw [h]; exact ⟨w, hw, rfl⟩
      obtain ⟨j, hj, hjw⟩ := h1
      have hz : j⁻¹ * w ∈ P ⊓ fixV Mp := by
        refine ⟨P.mul_mem (P.inv_mem (hJP hj)) hw, (hker _).1 ?_⟩
        rw [map_mul, map_inv, hjw, inv_mul_cancel]
      rw [hPZ, Subgroup.mem_bot] at hz
      have : w = j := by
        have := congrArg (j * ·) hz
        simpa using this
      rw [this]
      exact hj

omit [Finite W] in
theorem tilde_lift (U : Subgroup W) {Y : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))}
    (hY : Y ≤ tilde Mp ⊤ U) :
    tilde Mp ⊤ (U ⊓ Y.comap (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)))) = Y := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact hw.2
  · obtain ⟨u, hu, rfl⟩ := hY hx
    exact ⟨u, ⟨hu, hx⟩, rfl⟩

theorem one_le_nSec_lift (hW : ∀ w : W, w ^ 2 = 1)
    (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))) {U U' : Subgroup W}
    {B : Subgroup (MulAut W)} (hBM : B ≤ M) {Y Y' : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))}
    (hY' : Y' ≤ tilde Mp ⊤ U) (hUU' : U' ⊓ U ≤ fixV Mp) {a : MulAut W} (ha : a ∈ B)
    (haU : ∀ u ∈ U, a u ∈ U)
    (hmove : letI := qAct hMp; ∃ q ∈ Y', (⟨a, hBM ha⟩ : ↥M) • q * q⁻¹ ∉ Y) :
    1 ≤ nSec B (U' ⊔ U ⊓ Y'.comap (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))))
      (U' ⊔ U ⊓ Y.comap (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)))) := by
  let _i := qAct hMp
  set κ := QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) with hκ
  have hker : ∀ w : W, κ w = 1 ↔ w ∈ fixV Mp := by
    intro w
    rw [hκ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq]
  obtain ⟨q, hq, hmv⟩ := hmove
  obtain ⟨w, hw, rfl⟩ := hY' hq
  have hwmem : w ∈ U' ⊔ U ⊓ Y'.comap κ := Subgroup.mem_sup_right ⟨hw, hq⟩
  refine one_le_nSec hW ha hwmem fun hmem => hmv ?_
  obtain ⟨u', hu', p, hp, he⟩ := Subgroup.mem_sup.1 hmem
  have hcU : a w * w⁻¹ ∈ U := U.mul_mem (haU w hw) (U.inv_mem hw)
  have hu'U : u' ∈ U := by
    have : u' = (a w * w⁻¹) * p⁻¹ := by rw [← he]; group
    rw [this]
    exact U.mul_mem hcU (U.inv_mem hp.1)
  have hu'1 : κ u' = 1 := (hker u').2 (hUU' ⟨hu', hu'U⟩)
  have h1 : κ (a w * w⁻¹) = κ p := by rw [← he, map_mul, hu'1, one_mul]
  have h2 : κ (a w * w⁻¹) = (⟨a, hBM ha⟩ : ↥M) • κ w * (κ w)⁻¹ := by
    rw [map_mul, map_inv]
    rfl
  rw [← h2, h1]
  exact hp.2

end Lift2

section Side

variable {W : Type} [CommGroup W] [Finite W] {M Mp : Subgroup (MulAut W)}

theorem side_count (hW : ∀ w : W, w ^ 2 = 1)
    (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))) {X : Subgroup (MulAut W)}
    (hXM : X ≤ M) (hXs : IsSimpleGroup ↥X) (hXperf : ⁅X, X⁆ = X)
    (hUZ : commV X ⊓ fixV Mp = commV X ⊓ fixV X)
    {V : Subgroup W} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 1)
    {π : ↥(StatedSL 3 K) →* ↥X}
    (hR : (FFModel.nat (StatedSL 3 K)).RealizesVia X V (V ⊓ fixV Mp) π)
    (hIirr : letI := qAct hMp; XMod.IsIrr ↥(X.subgroupOf M) (tilde Mp ⊤ V))
    (hY : letI := qAct hMp;
      IsotypicOfLength ↥(X.subgroupOf M) (tilde Mp ⊤ (commV X)) (tilde Mp ⊤ V) 4)
    (hcommQ : letI := qAct hMp; ∀ R ≤ tilde Mp ⊤ (commV X), XMod.IsInv ↥(X.subgroupOf M) R →
      XMod.commOf ↥(X.subgroupOf M) R = R)
    (hsplit : ∀ P ≤ commV X, XMod.IsIrr ↥X P → P ⊓ fixV Mp = ⊥ → False)
    {A : Subgroup (MulAut W)} (hAM : A ≤ M) (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    rk ↥A ≤ rk ↥(A ⊓ Subgroup.centralizer (X : Set (MulAut W))) + 2 ∧
    (¬ A ≤ Subgroup.centralizer (X : Set (MulAut W)) →
      5 ≤ nSec A (commV X) ⊥ ∧
      ∀ U' : Subgroup W, (∀ a ∈ A, ∀ w ∈ U', a w ∈ U') → U' ⊓ commV X ≤ fixV Mp →
        4 ≤ nSec A (U' ⊔ commV X) U') := by
  let _i := qAct hMp
  set U := commV X with hU
  set κ := QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) with hκ
  have hker : ∀ w : W, κ w = 1 ↔ w ∈ fixV Mp := by
    intro w
    rw [hκ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq]
  set Λ := X.subgroupOf M with hΛ
  set A' := A.subgroupOf M with hA'
  have hQ := quot_sq_of hW (modFix Mp (⊤ : Subgroup W))
  have hA'2 : IsPGroup 2 ↥A' := fun a => ⟨1, Subtype.ext (Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_pow]
    exact hA2 _ (Subgroup.mem_subgroupOf.1 a.2)))⟩
  have hA'Λ : ∀ a ∈ A', ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ := fun a ha l hl =>
    Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 (hAX (Subgroup.mem_subgroupOf.1 ha))
      _).1 (Subgroup.mem_subgroupOf.1 hl))
  have hAU : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := fun a ha u hu => B15P4.map_commV_mem (hAX ha) u hu
  have hXU : ∀ x ∈ X, ∀ u ∈ U, x u ∈ U := fun x hx u hu =>
    B15P4.map_commV_mem (Subgroup.le_normalizer hx) u hu
  have hA'Y : ∀ a ∈ A', ∀ q ∈ tilde Mp ⊤ U, a • q ∈ tilde Mp ⊤ U := by
    rintro a ha _ ⟨u, hu, rfl⟩
    exact ⟨_, hAU _ (Subgroup.mem_subgroupOf.1 ha) u hu, rfl⟩
  obtain ⟨Y₁, Y₂, Y₃, hY₁, hY₁₂, hY₂₃, hY₃Y, hY₂i, hY₃i, hY₁A, hY₂A, hY₃A⟩ :=
    exists_chain_four hQ hIirr hY hA'2 hA'Λ hA'Y
  have hY₃le : Y₃ ≤ tilde Mp ⊤ U := hY₃Y.1.le
  have hY₂le : Y₂ ≤ tilde Mp ⊤ U := hY₂₃.1.le.trans hY₃le
  have hY₁le : Y₁ ≤ tilde Mp ⊤ U := hY₁₂.1.le.trans hY₂le
  set L₁ := U ⊓ Y₁.comap κ with hL₁
  have hL₁X : ∀ x ∈ X, ∀ v ∈ L₁, x v ∈ L₁ := fun x hx v hv =>
    ⟨hXU x hx v hv.1, hY₁.1 ⟨⟨x, hXM hx⟩, Subgroup.mem_subgroupOf.2 hx⟩ (κ v) hv.2⟩
  have hL₁A : ∀ a ∈ A, ∀ v ∈ L₁, a v ∈ L₁ := fun a ha v hv =>
    ⟨hAU a ha v hv.1, hY₁A ⟨a, hAM ha⟩ (Subgroup.mem_subgroupOf.2 ha) (κ v) hv.2⟩
  set P' := commSub L₁ X with hP'
  have hP'L₁ : P' ≤ L₁ := commSub_le_of_invariant hL₁X
  have hP'U : P' ≤ U := hP'L₁.trans inf_le_left
  have hP'X : ∀ x ∈ X, ∀ v ∈ P', x v ∈ P' := commSub_isInv L₁ X
  have hP'A : ∀ a ∈ A, ∀ v ∈ P', a v ∈ P' := fun a ha => commSub_stab (hAX ha) (hL₁A a ha)
  have hP'comm : XMod.commOf ↥X P' = P' := by
    rw [commOf_eq_commSub, hP', SmithD310U.commSub_commSub_eq hXperf]
  have htP' : tilde Mp ⊤ P' = Y₁ := by
    rw [hP', tilde_commSub hMp hXM, tilde_lift U hY₁le]
    exact hcommQ Y₁ hY₁le hY₁.1
  have hP'Z : P' ⊓ fixV Mp = P' ⊓ fixV X := by
    rw [← inf_eq_left.2 hP'U, inf_assoc, inf_assoc, hUZ]
  have hiso : XMod.Iso ↥Λ (tilde Mp ⊤ P') (tilde Mp ⊤ V) := by
    rw [htP']
    exact iso_of_le_isoComp hY₁ (hY₁le.trans hY.2.1)
  have hRP' := realizesVia_of_iso_tilde hMp hXM hR hP'X hiso
  have hnatP' : BinaryNaturalSL X P' (P' ⊓ fixV X) 3 1 :=
    ⟨K, inferInstance, inferInstance, hK, π, by rw [← hP'Z]; exact hRP'⟩
  have hP'ne : P' ⊓ fixV Mp ≠ ⊥ := by
    intro h
    exact hsplit P' hP'U (isIrr_of_tilde hMp hP'X h (htP' ▸ hY₁)) h
  have hP'2 : Nat.card ↥(P' ⊓ fixV X) = 2 := by
    have h1 := card_fixV_le_two_of_natural3 hW X P' hP'X hP'comm hnatP'
    have h2 : P' ⊓ fixV X ≠ ⊥ := by rw [← hP'Z]; exact hP'ne
    have h3 : 1 < Nat.card ↥(P' ⊓ fixV X) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact h2
    have h4 := card_eq_two_pow hW (P' ⊓ fixV X)
    rw [h4] at h1 h3 ⊢
    have : rk ↥(P' ⊓ fixV X) ≤ 1 := by
      by_contra hc
      push Not at hc
      have : 2 ^ 2 ≤ 2 ^ rk ↥(P' ⊓ fixV X) := Nat.pow_le_pow_right (by norm_num) hc
      omega
    interval_cases h : rk ↥(P' ⊓ fixV X) <;> simp_all
  have hAP' : ∀ a ∈ A, ∀ v, a v ∈ P' ↔ v ∈ P' := by
    intro a ha v
    refine ⟨fun h => ?_, hP'A a ha v⟩
    have h1 := hP'A a ha _ h
    have h2 : a (a v) = v := by
      rw [← MulAut.mul_apply, ← pow_two, hA2 a ha]
      rfl
    rwa [h2] at h1
  refine ⟨rk_le_add_two_of_cover hW hP'X hP'comm hnatP' hP'2 hAX hAP' hA2 hAc, fun hnc => ?_⟩
  have hnc' : ¬ ∀ a ∈ A, ∀ x ∈ X, a * x = x * a := fun h =>
    hnc fun a ha => Subgroup.mem_centralizer_iff.2 fun x hx => (h a ha x hx).symm
  have h2 := two_le_nSec_cover hW hP'X hP'comm hnatP' hP'2 hAX hAP' hA2 hnc'
  have hΛs : IsSimpleGroup ↥Λ := (Subgroup.subgroupOfEquivOfLe hXM).isSimpleGroup
  have hmove : ∀ J J' : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)), J < J' →
      J' ≤ tilde Mp ⊤ U → XMod.IsInv ↥Λ J → XMod.IsInv ↥Λ J' →
      (∀ a ∈ A', ∀ q ∈ J, a • q ∈ J) → (∀ a ∈ A', ∀ q ∈ J', a • q ∈ J') →
      ∃ a ∈ A', ∃ q ∈ J', a • q * q⁻¹ ∉ J := by
    intro J J' hJJ' hJ'U hJΛ hJ'Λ hJA hJ'A
    rcases comm_or_exists_moved hΛs hA'Λ hJJ' hJΛ hJ'Λ hJA (hcommQ J' hJ'U hJ'Λ) with
      h | h
    · exfalso
      apply hnc'
      intro a ha x hx
      have h1 := h ⟨a, hAM ha⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨x, hXM hx⟩
        (Subgroup.mem_subgroupOf.2 hx)
      exact congrArg Subtype.val h1
    · exact h
  have hstep : ∀ (U' : Subgroup W), U' ⊓ U ≤ fixV Mp →
      ∀ J J' : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)), J < J' →
      J' ≤ tilde Mp ⊤ U → XMod.IsInv ↥Λ J → XMod.IsInv ↥Λ J' →
      (∀ a ∈ A', ∀ q ∈ J, a • q ∈ J) → (∀ a ∈ A', ∀ q ∈ J', a • q ∈ J') →
      1 ≤ nSec A (U' ⊔ U ⊓ J'.comap κ) (U' ⊔ U ⊓ J.comap κ) := by
    intro U' hU' J J' hJJ' hJ'U hJΛ hJ'Λ hJA hJ'A
    obtain ⟨a, ha, q, hq, hmv⟩ := hmove J J' hJJ' hJ'U hJΛ hJ'Λ hJA hJ'A
    exact one_le_nSec_lift hW hMp hAM hJ'U hU' (Subgroup.mem_subgroupOf.1 ha)
      (hAU _ (Subgroup.mem_subgroupOf.1 ha)) ⟨q, hq, hmv⟩
  set L₂ := U ⊓ Y₂.comap κ with hL₂
  set L₃ := U ⊓ Y₃.comap κ with hL₃
  set L₀ := U ⊓ (⊥ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))).comap κ with hL₀
  have hL₄ : U ⊓ (tilde Mp ⊤ U).comap κ = U :=
    inf_eq_left.2 fun u hu => ⟨u, hu, rfl⟩
  have hlift_A : ∀ J : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)),
      (∀ a ∈ A', ∀ q ∈ J, a • q ∈ J) → ∀ a ∈ A, ∀ v ∈ U ⊓ J.comap κ, a v ∈ U ⊓ J.comap κ :=
    fun J hJ a ha v hv =>
      ⟨hAU a ha v hv.1, hJ ⟨a, hAM ha⟩ (Subgroup.mem_subgroupOf.2 ha) (κ v) hv.2⟩
  have hbotA : ∀ a ∈ A', ∀ q ∈ (⊥ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))), a • q ∈
      (⊥ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) := by
    intro a _ q hq
    rw [Subgroup.mem_bot] at hq ⊢
    rw [hq, smul_one]
  have hQA : ∀ a ∈ A', ∀ q ∈ tilde Mp ⊤ U, a • q ∈ tilde Mp ⊤ U := hA'Y
  have hL₂A := hlift_A Y₂ hY₂A
  have hL₃A := hlift_A Y₃ hY₃A
  have hL₀A := hlift_A ⊥ hbotA
  have hL₁L₂ : L₁ ≤ L₂ := inf_le_inf_left _ (Subgroup.comap_mono hY₁₂.1.le)
  have hL₂L₃ : L₂ ≤ L₃ := inf_le_inf_left _ (Subgroup.comap_mono hY₂₃.1.le)
  have hL₃U : L₃ ≤ U := inf_le_left
  have hL₀L₁ : L₀ ≤ L₁ := inf_le_inf_left _ (Subgroup.comap_mono bot_le)
  have hsupA : ∀ H H' : Subgroup W, (∀ a ∈ A, ∀ w ∈ H, a w ∈ H) →
      (∀ a ∈ A, ∀ w ∈ H', a w ∈ H') → ∀ a ∈ A, ∀ w ∈ H ⊔ H', a w ∈ H ⊔ H' := by
    intro H H' hH hH' a ha w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hH a ha x hx) (hH' a ha y hy)
  have hs : ∀ U' : Subgroup W, U' ⊓ U ≤ fixV Mp →
      1 ≤ nSec A (U' ⊔ L₁) (U' ⊔ L₀) ∧ 1 ≤ nSec A (U' ⊔ L₂) (U' ⊔ L₁) ∧
        1 ≤ nSec A (U' ⊔ L₃) (U' ⊔ L₂) ∧ 1 ≤ nSec A (U' ⊔ U) (U' ⊔ L₃) := by
    intro U' hU'
    refine ⟨hstep U' hU' ⊥ Y₁ hY₁.2.1 hY₁le XMod.isInv_bot hY₁.1 hbotA hY₁A,
      hstep U' hU' Y₁ Y₂ hY₁₂.1 hY₂le hY₁.1 hY₂i hY₁A hY₂A,
      hstep U' hU' Y₂ Y₃ hY₂₃.1 hY₃le hY₂i hY₃i hY₂A hY₃A, ?_⟩
    have := hstep U' hU' Y₃ (tilde Mp ⊤ U) hY₃Y.1 le_rfl hY₃i hY.1 hY₃A hQA
    rwa [hL₄] at this
  refine ⟨?_, fun U' hU'A hU'U => ?_⟩
  · obtain ⟨-, s₂, s₃, s₄⟩ := hs ⊥ (by rw [bot_inf_eq]; exact bot_le)
    simp only [bot_sup_eq] at s₂ s₃ s₄
    have e1 := nSec_add_le A (bot_le : (⊥ : Subgroup W) ≤ P') hP'U hP'A
    have e2 := nSec_add_le A hP'L₁ (hL₁L₂.trans (hL₂L₃.trans hL₃U)) hL₁A
    have e3 := nSec_add_le A hL₁L₂ (hL₂L₃.trans hL₃U) hL₂A
    have e4 := nSec_add_le A hL₂L₃ hL₃U hL₃A
    omega
  · obtain ⟨s₁, s₂, s₃, s₄⟩ := hs U' hU'U
    have hA0 := hsupA U' L₀ hU'A hL₀A
    have hA1 := hsupA U' L₁ hU'A hL₁A
    have hA2' := hsupA U' L₂ hU'A hL₂A
    have hA3 := hsupA U' L₃ hU'A hL₃A
    have m0 : U' ⊔ L₀ ≤ U' ⊔ L₁ := sup_le_sup_left hL₀L₁ _
    have m1 : U' ⊔ L₁ ≤ U' ⊔ L₂ := sup_le_sup_left hL₁L₂ _
    have m2 : U' ⊔ L₂ ≤ U' ⊔ L₃ := sup_le_sup_left hL₂L₃ _
    have m3 : U' ⊔ L₃ ≤ U' ⊔ U := sup_le_sup_left hL₃U _
    have e0 := nSec_add_le A (le_sup_left : U' ≤ U' ⊔ L₀) (m0.trans (m1.trans (m2.trans m3))) hA0
    have e1 := nSec_add_le A m0 (m1.trans (m2.trans m3)) hA1
    have e2 := nSec_add_le A m1 (m2.trans m3) hA2'
    have e3 := nSec_add_le A m2 m3 hA3
    omega

end Side

section Final

variable {W : Type} [CommGroup W] [Finite W] {M Mp : Subgroup (MulAut W)}

omit [Finite W] in
theorem rk_tilde_eq_three {X : Subgroup (MulAut W)} {V : Subgroup W} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ 1) {π : ↥(StatedSL 3 K) →* ↥X}
    (hR : (FFModel.nat (StatedSL 3 K)).RealizesVia X V (V ⊓ fixV Mp) π) [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) :
    rk ↥(tilde Mp ⊤ V) = 3 := by
  have h1 := G64.RealizesVia.card_eq hR
  rw [G64.card_natMod, hK] at h1
  have h2 : Nat.card ↥(tilde Mp ⊤ V) * Nat.card ↥(V ⊓ fixV Mp) = Nat.card ↥V := by
    rw [Nat.card_congr (tildeEquiv V).toEquiv, ← Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : V ⊓ fixV Mp ≤ V)).toEquiv,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have h3 : Nat.card ↥(tilde Mp ⊤ V) = 8 := by
    have hpos : 0 < Nat.card ↥(V ⊓ fixV Mp) := Nat.card_pos
    rw [h1] at h2
    have : Nat.card ↥(tilde Mp ⊤ V) * Nat.card ↥(V ⊓ fixV Mp) =
        8 * Nat.card ↥(V ⊓ fixV Mp) := by rw [h2]; norm_num
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [card_eq_two_pow (quot_sq_of hW _)] at h3
  exact Nat.pow_right_injective le_rfl (h3.trans (by norm_num : (8 : ℕ) = 2 ^ 3))

end Final

section Final2

variable {W : Type} [CommGroup W] [Finite W] {M Mp : Subgroup (MulAut W)}

structure SideHyp (hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)))
    (X : Subgroup (MulAut W)) (V : Subgroup W) : Prop where
  le : X ≤ M
  le_Mp : X ≤ Mp
  simple : IsSimpleGroup ↥X
  perfect : ⁅X, X⁆ = X
  inf_fixV : commV X ⊓ fixV Mp = commV X ⊓ fixV X
  nat : ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StatedSL 3 K) →* ↥X),
    Nat.card K = 2 ^ 1 ∧ (FFModel.nat (StatedSL 3 K)).RealizesVia X V (V ⊓ fixV Mp) π
  irr : letI := qAct hMp; XMod.IsIrr ↥(X.subgroupOf M) (tilde Mp ⊤ V)
  homog : letI := qAct hMp;
    IsotypicOfLength ↥(X.subgroupOf M) (tilde Mp ⊤ (commV X)) (tilde Mp ⊤ V) 4
  comm : letI := qAct hMp; ∀ R ≤ tilde Mp ⊤ (commV X), XMod.IsInv ↥(X.subgroupOf M) R →
    XMod.commOf ↥(X.subgroupOf M) R = R
  five : ∃ (y : MulAut W) (hy : y ∈ M), (∀ l ∈ X, y * l = l * y) ∧
    (letI := qAct hMp; ∀ q ∈ tilde Mp ⊤ (commV X), (⟨y, hy⟩ : ↥M) ^ 5 • q = q) ∧
    (letI := qAct hMp; ∃ q ∈ tilde Mp ⊤ (commV X), (⟨y, hy⟩ : ↥M) • q ≠ q)

theorem SideHyp.no_split (hW : ∀ w : W, w ^ 2 = 1)
    {hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))} {X : Subgroup (MulAut W)}
    {V : Subgroup W} (hS : SideHyp hMp X V) (hZ : commV X ⊓ fixV Mp ≠ ⊥) :
    ∀ P ≤ commV X, XMod.IsIrr ↥X P → P ⊓ fixV Mp = ⊥ → False := by
  intro P hPU hP hPZ
  obtain ⟨K, _, _, π, hK, hR⟩ := hS.nat
  obtain ⟨y, hyM, hyX, hy5, hy1⟩ := hS.five
  have hodd : Odd (rk ↥(tilde Mp ⊤ V)) := by
    rw [rk_tilde_eq_three hK hR hW]
    decide
  exact hZ (inf_fixV_eq_bot_of_split hW hMp hS.le_Mp hS.perfect hS.inf_fixV hS.irr hodd
    hS.homog hyM hyX hy5 hy1 hPU hP hPZ)

end Final2

section Final3

variable {W : Type} [CommGroup W] [Finite W] {M Mp : Subgroup (MulAut W)}

omit [Finite W] in
theorem commV_conjAutSub (t : MulAut W) (X : Subgroup (MulAut W)) :
    commV (conjAutSub t X) = (commV X).map t.toMonoidHom :=
  CFSG.Quasithin.commV_map_conj_eq X t

theorem commV_inf_fixV_eq_bot (hW : ∀ w : W, w ^ 2 = 1)
    {hMp : M ≤ Subgroup.normalizer (Mp : Set (MulAut W))} {L L' : Subgroup (MulAut W)}
    {V V' : Subgroup W} {t : MulAut W} (htM : t ∈ M) (hL' : L' = conjAutSub t L)
    (hS : SideHyp hMp L V) (hS' : SideHyp hMp L' V') (hUU : commV L ⊓ commV L' ≤ fixV Mp)
    {A : Subgroup (MulAut W)} (hAM : A ≤ M) (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hAL' : A ≤ Subgroup.normalizer (L' : Set (MulAut W))) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA1 : A ≠ ⊥) (hAr : nSec A ⊤ ⊥ ≤ 2 * rk ↥A)
    (hAC : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ⊓
      Subgroup.centralizer (L' : Set (MulAut W)) = ⊥) :
    commV L ⊓ fixV Mp = ⊥ := by
  by_contra hZ
  have htZ : ∀ w ∈ fixV Mp, t w ∈ fixV Mp := by
    intro w hw
    refine mem_fixV.2 fun x hx => ?_
    have hx' : t⁻¹ * x * t ∈ Mp := (Subgroup.mem_normalizer_iff''.1 (hMp htM) x).1 hx
    have h1 : (t⁻¹ * x * t) w = w := mem_fixV.1 hw _ hx'
    calc x (t w) = t ((t⁻¹ * x * t) w) := by simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      _ = t w := by rw [h1]
  have hZ' : commV L' ⊓ fixV Mp ≠ ⊥ := by
    intro h
    apply hZ
    rw [eq_bot_iff]
    intro w hw
    have h1 : t w ∈ commV L' ⊓ fixV Mp := by
      rw [hL', commV_conjAutSub]
      exact ⟨⟨w, hw.1, rfl⟩, htZ w hw.2⟩
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact (map_eq_one_iff t (MulEquiv.injective t)).1 h1
  obtain ⟨K, _, _, π, hK, hR⟩ := hS.nat
  obtain ⟨K', _, _, π', hK', hR'⟩ := hS'.nat
  obtain ⟨hrk, hcnt⟩ := side_count hW hMp hS.le hS.simple hS.perfect hS.inf_fixV hK hR hS.irr
    hS.homog hS.comm (hS.no_split hW hZ) hAM hAL hA2 hAc
  obtain ⟨hrk', hcnt'⟩ := side_count hW hMp hS'.le hS'.simple hS'.perfect hS'.inf_fixV hK' hR'
    hS'.irr hS'.homog hS'.comm (hS'.no_split hW hZ') hAM hAL' hA2 hAc
  have hsum : rk ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) +
      rk ↥(A ⊓ Subgroup.centralizer (L' : Set (MulAut W))) ≤ rk ↥A := by
    have h1 := B2F.rk_sup_add_rk_inf_of_commute (A := A ⊓ Subgroup.centralizer (L : Set _))
      (B := A ⊓ Subgroup.centralizer (L' : Set _)) fun a ha b hb => hAc a ha.1 b hb.1
    have h2 : (A ⊓ Subgroup.centralizer (L : Set (MulAut W))) ⊓
        (A ⊓ Subgroup.centralizer (L' : Set (MulAut W))) = ⊥ := by
      rw [← hAC]
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [h2, rk_bot] at h1
    have h3 := rk_mono (sup_le (inf_le_left : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ≤ A)
      (inf_le_left : A ⊓ Subgroup.centralizer (L' : Set (MulAut W)) ≤ A))
    omega
  have hmono : ∀ H : Subgroup W, (∀ a ∈ A, ∀ w ∈ H, a w ∈ H) → nSec A H ⊥ ≤ nSec A ⊤ ⊥ := by
    intro H hH
    have := nSec_add_le A (bot_le : (⊥ : Subgroup W) ≤ H) le_top hH
    omega
  have hAU : ∀ a ∈ A, ∀ u ∈ commV L, a u ∈ commV L := fun a ha u hu =>
    B15P4.map_commV_mem (hAL ha) u hu
  have hAU' : ∀ a ∈ A, ∀ u ∈ commV L', a u ∈ commV L' := fun a ha u hu =>
    B15P4.map_commV_mem (hAL' ha) u hu
  by_cases hcL : A ≤ Subgroup.centralizer (L : Set (MulAut W))
  · by_cases hcL' : A ≤ Subgroup.centralizer (L' : Set (MulAut W))
    · apply hA1
      rw [← hAC]
      exact le_antisymm (le_inf (le_inf le_rfl hcL) hcL') (inf_le_left.trans inf_le_left)
    · obtain ⟨h5, -⟩ := hcnt' hcL'
      have h0 : A ⊓ Subgroup.centralizer (L' : Set (MulAut W)) ≤
          A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ⊓
            Subgroup.centralizer (L' : Set (MulAut W)) :=
        fun x hx => ⟨⟨hx.1, hcL hx.1⟩, hx.2⟩
      rw [hAC, le_bot_iff] at h0
      rw [h0, rk_bot] at hrk'
      have := hmono _ hAU'
      omega
  · obtain ⟨h5, -⟩ := hcnt hcL
    by_cases hcL' : A ≤ Subgroup.centralizer (L' : Set (MulAut W))
    · have h0 : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ≤
          A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ⊓
            Subgroup.centralizer (L' : Set (MulAut W)) :=
        fun x hx => ⟨hx, hcL' hx.1⟩
      rw [hAC, le_bot_iff] at h0
      rw [h0, rk_bot] at hrk
      have := hmono _ hAU
      omega
    · obtain ⟨-, h4⟩ := hcnt' hcL'
      have h4' := h4 (commV L) hAU hUU
      have hsupA : ∀ a ∈ A, ∀ w ∈ commV L ⊔ commV L', a w ∈ commV L ⊔ commV L' := by
        intro a ha w hw
        obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hw
        rw [map_mul]
        exact Subgroup.mul_mem_sup (hAU a ha x hx) (hAU' a ha y hy)
      have e := nSec_add_le A (bot_le : (⊥ : Subgroup W) ≤ commV L)
        (le_sup_left : commV L ≤ commV L ⊔ commV L') hAU
      have := hmono _ hsupA
      omega

end Final3

end CFSG.Quasithin.SmithD321
