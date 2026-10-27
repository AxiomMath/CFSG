module

public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.EmptyFaithful.SmithD391Cent

public section

namespace CFSG.Quasithin.SmithD310U

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

section Abstract

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q] [Finite Q]
  {Λ : Subgroup Γ} {V : Subgroup Q}

omit [Finite Q] in
theorem exists_smul_inf_eq_bot (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    (hV : XMod.IsIrr ↥Λ V) (hgen : (⨆ g : Γ, g • V) = ⊤) {S : Subgroup Q}
    (hS : XMod.IsInv ↥Λ S) (hne : S ≠ ⊤) : ∃ g : Γ, S ⊓ g • V = ⊥ := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  by_contra hcon
  push Not at hcon
  apply hne
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun g => ?_
  have hinv : XMod.IsInv ↥Λ (S ⊓ g • V) := hS.inf (XMod.isInv_smul_of_normalizes hN g hV.1)
  rcases (isIrr_smul hN g hV).2.2 _ hinv bot_le inf_le_right with h | h
  · exact absurd h (hcon g)
  · rw [← h]
    exact inf_le_left

theorem rk_add_le_of_isInv (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hV : XMod.IsIrr ↥Λ V)
    (hgen : (⨆ g : Γ, g • V) = ⊤) {S : Subgroup Q} (hS : XMod.IsInv ↥Λ S) (hne : S ≠ ⊤) :
    rk ↥S + rk ↥V ≤ rk ↥(⊤ : Subgroup Q) := by
  obtain ⟨g, hg⟩ := exists_smul_inf_eq_bot hΛ hV hgen hS hne
  have h1 := rk_sup_add_rk_inf S (g • V)
  rw [hg, rk_bot, rk_smul] at h1
  have h2 := rk_mono (le_top : S ⊔ g • V ≤ ⊤)
  omega

theorem rk_dvd_of_isInv (hQ : ∀ q : Q, q ^ 2 = 1) (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    (hV : XMod.IsIrr ↥Λ V) (hgen : (⨆ g : Γ, g • V) = ⊤) {S : Subgroup Q}
    (hS : XMod.IsInv ↥Λ S) : rk ↥V ∣ rk ↥S := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  have hv : 0 < rk ↥V := by
    by_contra h0
    exact hV.2.1.ne' ((rk_eq_zero_iff hQ).1 (by omega))
  have key : ∀ n : ℕ, ∀ S : Subgroup Q, XMod.IsInv ↥Λ S →
      rk ↥(⊤ : Subgroup Q) - rk ↥S = n → rk ↥V ∣ rk ↥(⊤ : Subgroup Q) - rk ↥S := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hS hn
      by_cases htop : S = ⊤
      · rw [htop, Nat.sub_self]
        exact dvd_zero _
      · obtain ⟨g, hg⟩ := exists_smul_inf_eq_bot hΛ hV hgen hS htop
        have hinv : XMod.IsInv ↥Λ (S ⊔ g • V) :=
          hS.sup (XMod.isInv_smul_of_normalizes hN g hV.1)
        have h1 := rk_sup_add_rk_inf S (g • V)
        rw [hg, rk_bot, rk_smul] at h1
        have h2 := rk_mono (le_top : S ⊔ g • V ≤ ⊤)
        have h3 := ih _ (by omega) _ hinv rfl
        have h4 : rk ↥(⊤ : Subgroup Q) - rk ↥S =
            (rk ↥(⊤ : Subgroup Q) - rk ↥(S ⊔ g • V)) + rk ↥V := by omega
        rw [h4]
        exact dvd_add h3 dvd_rfl
  have h1 := key _ ⊥ XMod.isInv_bot rfl
  have h2 := key _ S hS rfl
  rw [rk_bot, Nat.sub_zero] at h1
  have h3 := rk_mono (le_top : S ≤ ⊤)
  have h4 : rk ↥S = rk ↥(⊤ : Subgroup Q) - (rk ↥(⊤ : Subgroup Q) - rk ↥S) := by omega
  rw [h4]
  exact Nat.dvd_sub h1 h2

omit [Finite Q] in
theorem isInv_fixed_of_comm {E : Subgroup Γ} (hEΛ : ∀ e ∈ E, ∀ l ∈ Λ, e * l = l * e) :
    XMod.IsInv ↥Λ (XMod.fixed ↥E (⊤ : Subgroup Q)) := by
  intro l q hq
  refine XMod.mem_fixed.2 ⟨trivial, fun e => ?_⟩
  show (e : Γ) • (l : Γ) • q = (l : Γ) • q
  rw [smul_smul, hEΛ e e.2 l l.2, mul_smul]
  exact congrArg _ ((XMod.mem_fixed.1 hq).2 e)

theorem rk_le_nB_of_comm (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hV : XMod.IsIrr ↥Λ V)
    (hgen : (⨆ g : Γ, g • V) = ⊤) {E : Subgroup Γ} (hEΛ : ∀ e ∈ E, ∀ l ∈ Λ, e * l = l * e)
    (hE : ∃ e ∈ E, ∃ q : Q, e • q ≠ q) : rk ↥V ≤ nB E (⊤ : Subgroup Q) := by
  have hS := isInv_fixed_of_comm (Q := Q) hEΛ
  have hne : XMod.fixed ↥E (⊤ : Subgroup Q) ≠ ⊤ := by
    obtain ⟨e, he, q, hq⟩ := hE
    intro h
    have : q ∈ XMod.fixed ↥E (⊤ : Subgroup Q) := by rw [h]; trivial
    exact hq ((XMod.mem_fixed.1 this).2 ⟨e, he⟩)
  have h1 := rk_add_le_of_isInv hΛ hV hgen hS hne
  unfold nB
  rw [top_inf_eq]
  omega

theorem three_le_rk_of_injective (hQ : ∀ q : Q, q ^ 2 = 1)
    (hV : ∀ l : ↥Λ, ∀ v ∈ V, l • v ∈ V) (hinj : Function.Injective (actAut Λ V hV))
    [Group.IsPerfect ↥Λ] [Nontrivial ↥Λ] : 3 ≤ rk ↥V := by
  by_contra hlt
  have hcard : Nat.card ↥V ≤ 4 := by
    rw [card_eq_two_pow hQ V]
    calc 2 ^ rk ↥V ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have : Group.IsSolvable (Equiv.Perm ↥V) := Equiv.Perm.isSolvable hcard
  have : Group.IsSolvable (MulAut ↥V) :=
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm _) fun a b hab =>
      MulEquiv.ext fun u => congrArg (fun e : Equiv.Perm _ => e u) hab
  have : Group.IsSolvable ↥Λ := Group.isSolvable_of_isSolvable_injective hinj
  exact Group.IsPerfect.not_isSolvable ↥Λ this

omit [Finite Q] in
theorem exists_inv_of_not_comm {G : Type*} [Group G] {P : Subgroup G} (hP : IsPGroup 3 ↥P)
    {b : G} (hb2 : b ^ 2 = 1) (hbP : ∀ g ∈ P, b * g * b⁻¹ ∈ P) {g : G} (hg : g ∈ P)
    (hbg : b * g ≠ g * b) : ∃ y ∈ P, y ^ 3 = 1 ∧ y ≠ 1 ∧ b * y * b⁻¹ = y⁻¹ := by
  classical
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hb2])
  set y₀ := g⁻¹ * (b * g * b⁻¹) with hy₀
  have hy₀P : y₀ ∈ P := P.mul_mem (P.inv_mem hg) (hbP g hg)
  have hy₀1 : y₀ ≠ 1 := by
    intro h
    apply hbg
    have h1 : b * g * b⁻¹ = g := by
      have := congrArg (g * ·) h
      simpa [hy₀, mul_assoc] using this
    calc b * g = b * g * b⁻¹ * b := by group
      _ = g * b := by rw [h1]
  have hy₀inv : b * y₀ * b⁻¹ = y₀⁻¹ := by
    have hbb : b * b = 1 := by rw [← pow_two, hb2]
    rw [hy₀]
    calc b * (g⁻¹ * (b * g * b⁻¹)) * b⁻¹ = b * g⁻¹ * b * g * (b * b)⁻¹ := by group
      _ = b * g⁻¹ * b * g := by rw [hbb, inv_one, mul_one]
      _ = b * g⁻¹ * b⁻¹ * g := by rw [hbinv]
      _ = (g⁻¹ * (b * g * b⁻¹))⁻¹ := by group
  obtain ⟨n₀, hn₀⟩ := hP ⟨y₀, hy₀P⟩
  have hex : ∃ n : ℕ, y₀ ^ 3 ^ n = 1 := ⟨n₀, by simpa using congrArg Subtype.val hn₀⟩
  set n := Nat.find hex with hn
  have hnspec : y₀ ^ 3 ^ n = 1 := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hnspec
    exact hy₀1 hnspec
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨y₀ ^ 3 ^ m, P.pow_mem hy₀P _, ?_, ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ, ← hm, hnspec]
  · intro h
    have hlt : m < n := by omega
    exact Nat.find_min hex hlt h
  · have h1 : b * y₀ ^ 3 ^ m * b⁻¹ = (b * y₀ * b⁻¹) ^ 3 ^ m := by
      rw [conj_pow]
    rw [h1, hy₀inv, inv_pow]

end Abstract

variable {W : Type} [CommGroup W] [Finite W]

section Situation

variable {M T L : Subgroup (MulAut W)} {V : Subgroup W}

omit [Finite W] in
theorem nB_anti {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]
    [Finite Q] {B A : Subgroup Γ} (hBA : B ≤ A) (S : Subgroup Q) : nB B S ≤ nB A S := by
  unfold nB
  have h1 : S ⊓ XMod.fixed ↥A (⊤ : Subgroup Q) ≤ S ⊓ XMod.fixed ↥B (⊤ : Subgroup Q) :=
    inf_le_inf_left _ fun q hq => XMod.mem_fixed.2 ⟨trivial, fun b =>
      (XMod.mem_fixed.1 hq).2 ⟨(b : Γ), hBA b.2⟩⟩
  have h2 := rk_mono h1
  have h3 := rk_mono (inf_le_left : S ⊓ XMod.fixed ↥B (⊤ : Subgroup Q) ≤ S)
  omega

omit [Finite W] in
theorem orbSup_eq_sup {t : MulAut W} (htT : t ∈ T)
    (hsplit : ∀ s ∈ T, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V) :
    orbSup T V = V ⊔ V.map t.toMonoidHom := by
  refine le_antisymm (orbSup_le fun s hs => ?_) (sup_le (le_orbSup T V) (map_le_orbSup htT))
  rcases hsplit s hs with h | h
  · rw [mem_stabSub_iff_map_eq.1 h]
    exact le_sup_left
  · rw [show s = t * (t⁻¹ * s) by group, map_mul_aut', mem_stabSub_iff_map_eq.1 h]
    exact le_sup_right

omit [Finite W] in
theorem fix_commSub_of_fix_quot {c : MulAut W} (hcL : ∀ l ∈ L, c * l = l * c)
    (hc : ∀ w ∈ V, c w * w⁻¹ ∈ fixV L) : ∀ x ∈ commSub V L, c x = x := by
  intro x hx
  unfold commSub at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, w, hw, rfl⟩ := hx
    obtain ⟨d, hd'⟩ : ∃ d : W, d = c w * w⁻¹ := ⟨_, rfl⟩
    have hd : d ∈ fixV L := hd' ▸ hc w hw
    have hcw : c w = d * w := by rw [hd']; group
    have hld : l d = d := (mem_fixV.1 hd) l hl
    have hcl : c (l w) = l (c w) := by
      have h1 := congrArg (fun φ : MulAut W => φ w) (hcL l hl)
      simpa [MulAut.mul_apply] using h1
    rw [map_mul, map_inv, hcl, hcw, map_mul, hld, mul_inv, mul_comm d (l w), mul_assoc,
      mul_inv_cancel_left]
  | one => exact map_one c
  | mul a b _ _ ha hb => rw [map_mul, ha, hb]
  | inv a _ ha => rw [map_inv, ha]

omit [Finite W] in
theorem fix_of_inv_comm (hirr : V ∈ IrrPlus L (⊤ : Subgroup W)) (hexp : ∀ w : W, w ^ 2 = 1)
    {c : MulAut W} (hcV : ∀ w ∈ V, c w ∈ V) (hc2 : c ^ 2 = 1) (hcL : ∀ l ∈ L, c * l = l * c) :
    ∀ w ∈ V, c w = w := by
  obtain ⟨hLV, hVcomm, -, hmax⟩ := mem_irrPlus_top_iff.1 hirr
  have hcl : ∀ l ∈ L, ∀ w : W, c (l w) = l (c w) := by
    intro l hl w
    have h1 := congrArg (fun φ : MulAut W => φ w) (hcL l hl)
    simpa [MulAut.mul_apply] using h1
  have hcc : ∀ w : W, c (c w) = w := by
    intro w
    have h1 := congrArg (fun φ : MulAut W => φ w) hc2
    simpa [pow_two, MulAut.mul_apply] using h1
  let f : W →* W := c.toMonoidHom / MonoidHom.id W
  have hf : ∀ w : W, f w = c w * w⁻¹ := fun w => div_eq_mul_inv _ _
  set J : Subgroup W := V ⊓ (fixV L).comap f with hJ
  have hmemJ : ∀ w : W, w ∈ J ↔ w ∈ V ∧ c w * w⁻¹ ∈ fixV L := by
    intro w
    rw [hJ, Subgroup.mem_inf, Subgroup.mem_comap, hf]
  have hJinv : ∀ x ∈ L, ∀ w ∈ J, x w ∈ J := by
    intro x hx w hw
    obtain ⟨hwV, hwf⟩ := (hmemJ w).1 hw
    refine (hmemJ _).2 ⟨hLV x hx w hwV, ?_⟩
    rw [hcl x hx, ← map_inv, ← map_mul, (mem_fixV.1 hwf) x hx]
    exact hwf
  have hCJ : V ⊓ fixV L ≤ J := by
    intro z hz
    refine (hmemJ z).2 ⟨hz.1, ?_⟩
    have hcz : c z ∈ fixV L := mem_fixV.2 fun l hl => by
      rw [← hcl l hl, (mem_fixV.1 hz.2) l hl]
    exact (fixV L).mul_mem hcz ((fixV L).inv_mem hz.2)
  have hJV : J ≤ V := inf_le_left
  have key : ∀ w ∈ V, c w * w⁻¹ ∈ fixV L := by
    intro w hw
    rcases hmax J hJinv hCJ hJV with h | h
    · have hu : c w * w⁻¹ ∈ J := by
        refine (hmemJ _).2 ⟨V.mul_mem (hcV w hw) (V.inv_mem hw), ?_⟩
        have h1 : c (c w * w⁻¹) * (c w * w⁻¹)⁻¹ = (w * (c w)⁻¹) ^ 2 := by
          rw [map_mul, map_inv, hcc, pow_two, mul_inv_rev, inv_inv]
        rw [h1, hexp]
        exact (fixV L).one_mem
      rw [h] at hu
      exact hu.2
    · rw [← h] at hw
      exact ((hmemJ w).1 hw).2
  intro w hw
  have h1 := fix_commSub_of_fix_quot hcL key w (by rw [hVcomm]; exact hw)
  exact h1

theorem mem_stabSub_of_comm (hD : D3Std M L T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g) {t : MulAut W} (htT : t ∈ T)
    (htn : t ∉ stabSub V) (hsplit : ∀ s ∈ T, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V)
    {c : MulAut W} (hcT : c ∈ T) (hcL : ∀ l ∈ L, c * l = l * c) : c ∈ stabSub V := by
  let _i := qAct hD.hyp.Mp_normal
  have hTM : T ≤ M := hD.hyp.sylow.1
  rcases hsplit c hcT with h | h
  · exact h
  · exfalso
    have hcV : V.map c.toMonoidHom = V.map t.toMonoidHom := by
      rw [show c = t * (t⁻¹ * c) by group, map_mul_aut', mem_stabSub_iff_map_eq.1 h]
    have hiso : XMod.Iso ↥(L.subgroupOf M) ((⟨c, hTM hcT⟩ : ↥M) • tilde L ⊤ V) (tilde L ⊤ V) :=
      iso_smul_of_comm (isIrr_tildeQ hD).1 fun l hl => Subtype.ext (hcL _ hl)
    have heq : (⟨c, hTM hcT⟩ : ↥M) • tilde L ⊤ V = (⟨t, hTM htT⟩ : ↥M) • tilde L ⊤ V := by
      rw [smul_tildeQ hD.hyp.Mp_normal, smul_tildeQ hD.hyp.Mp_normal]
      exact congrArg (tilde L ⊤) hcV
    rw [heq] at hiso
    exact not_iso_tildeQ hD hlt hC htT (hTM htT) htn hiso

theorem fix_orbSup_of_comm (hD : D3Std M L T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g) {t : MulAut W} (htT : t ∈ T)
    (htn : t ∉ stabSub V) (hsplit : ∀ s ∈ T, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V)
    {c : MulAut W} (hcT : c ∈ T) (hc2 : c ^ 2 = 1) (hcL : ∀ l ∈ L, c * l = l * c) :
    ∀ w ∈ orbSup T V, c w = w := by
  have hTn := d391_T_le hD
  have key : ∀ s ∈ T, s ^ 2 = 1 → (∀ l ∈ L, s * l = l * s) → ∀ v ∈ V, s v = v := by
    intro s hsT hs2 hsL
    have hsV := mem_stabSub_of_comm hD hlt hC htT htn hsplit hsT hsL
    exact fix_of_inv_comm hD.hyp.irr hD.hyp.exp (fun w hw => (hsV w).2 hw) hs2 hsL
  have hc'T : t⁻¹ * c * t ∈ T := T.mul_mem (T.mul_mem (T.inv_mem htT) hcT) htT
  have hc'2 : (t⁻¹ * c * t) ^ 2 = 1 := by
    have h1 : t⁻¹ * c * t = (MulAut.conj t⁻¹) c := by simp
    rw [h1, ← map_pow, hc2, map_one]
  have hc'L : ∀ l ∈ L, (t⁻¹ * c * t) * l = l * (t⁻¹ * c * t) := by
    intro l hl
    have h1 := hcL _ (((Subgroup.mem_normalizer_iff.1 (hTn htT)) l).1 hl)
    calc t⁻¹ * c * t * l = t⁻¹ * (c * (t * l * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * l * t⁻¹) * c) * t := by rw [h1]
      _ = l * (t⁻¹ * c * t) := by group
  have h1 := key c hcT hc2 hcL
  have h2 := key _ hc'T hc'2 hc'L
  intro w hw
  rw [orbSup_eq_sup htT hsplit] at hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hw
  obtain ⟨v, hv, rfl⟩ := hy
  rw [map_mul, h1 x hx]
  congr 1
  have h3 := h2 v hv
  have h4 : t (t⁻¹ (c (t v))) = t v := by
    simpa [MulAut.mul_apply] using congrArg t h3
  simpa using h4

theorem comm_of_fix (hD : D3Std M L T L V)
    (hC : ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g) {a : MulAut W} (haT : a ∈ T)
    (haV : ∀ v ∈ V, a v = v) : ∀ l ∈ L, a * l = l * a := by
  have hperf : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := hD.hyp.quasi.1
    exact Subgroup.commutator_eq_self
  have haN : ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun l hl =>
    ((Subgroup.mem_normalizer_iff.1 (d391_T_le hD haT)) l).1 hl
  obtain ⟨hLV, -, -, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hainv : ∀ v ∈ V, a⁻¹ v = v := by
    intro v hv
    calc a⁻¹ v = a⁻¹ (a v) := by rw [haV v hv]
      _ = v := MulAut.inv_apply_self W a v
  refine B5.commute_of_comm_central hperf haN
    (Z := L ⊓ Subgroup.centralizer (L : Set (MulAut W))) ?_ ?_
  · intro z hz l hl
    exact ((Subgroup.mem_centralizer_iff.1 hz.2) l hl).symm
  · intro l hl
    have hcL : ⁅a, l⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem (haN l hl) (L.inv_mem hl)
    refine ⟨hcL, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    refine (hC _ hcL (fun v hv => ?_) x hx).symm
    have h1 : l⁻¹ v ∈ V := hLV l⁻¹ (L.inv_mem hl) v hv
    simp only [commutatorElement_def, MulAut.mul_apply]
    rw [hainv _ h1, MulAut.apply_inv_self, haV v hv]

theorem commutator_pCoreOf_eq_bot (hexp : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} {r : ℚ} (hr : qhatOf M = (r : WithTop ℚ)) (hA : A ∈ QhatStar M)
    (hrk : 2 ≤ rk ↥A) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ⁅CFSG.Open.pCoreOf p M, A⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra h
  obtain ⟨h1, h2, -⟩ := D2_13 hexp hr hA (p := p) (by omega) rfl h
  have hp5' : p = 5 := by rcases h1 with h | h <;> omega
  have := (h2 hp5').2.1
  omega

end Situation

structure D310USit (M T L : Subgroup (MulAut W)) (V : Subgroup W) (t : MulAut W)
    (A : Subgroup (MulAut W)) (r : ℚ) (k : ℕ) : Prop where
  hD : D3Std M L T L V
  hr : qhatOf M = (r : WithTop ℚ)
  hr2 : r ≤ 2
  hlt : V < orbSup T V
  htop : orbSup T V ≠ ⊤
  hC : ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g
  htT : t ∈ T
  htn : t ∉ stabSub V
  hsplit : ∀ s ∈ T, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V
  hsum : IsSumMod (orbSup T V ⊓ fixV L) V (V.map t.toMonoidHom) (orbSup T V)
  hVT : orbSup T V = V ⊔ V.map t.toMonoidHom
  h5 : D35Five L V
  hk : letI := qAct hD.hyp.Mp_normal
    rk ↥(isoSum (L.subgroupOf M) (tilde L ⊤ V)) = k * rk ↥(tilde L ⊤ V)
  hk2 : 2 ≤ k
  hv3 : 3 ≤ rk ↥(tilde L ⊤ V)
  hAQ : A ∈ QhatStar M
  hAT : A ≤ T
  hAr : rAV A = r
  hB : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ≠ ⊥
  hrkA : 2 ≤ rk ↥A
  hCT : ∀ c ∈ T, c ^ 2 = 1 → (∀ l ∈ L, c * l = l * c) → ∀ w ∈ orbSup T V, c w = w
  hTV : ∀ a ∈ T, (∀ v ∈ V, a v = v) → ∀ l ∈ L, a * l = l * a
  hOp : ∀ p : ℕ, p.Prime → 5 ≤ p → ⁅CFSG.Open.pCoreOf p M, A⁆ = ⊥

theorem d310USit_of (h35 : D35) {M T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M L T L V) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ)) (hlt : V < orbSup T V)
    (hunf : ∀ A : Subgroup (MulAut W), IsA2 M A → A ≤ T → commSeries A 3 = ⊥ → rAV A ≤ 2 →
      ∃ a ∈ A, a ≠ 1 ∧ ∀ x ∈ L, a * x = x * a)
    (htop : orbSup T V ≠ ⊤) : ∃ t A r k, D310USit M T L V t A r k := by
  let _i := qAct hD.hyp.Mp_normal
  have hexp := hD.hyp.exp
  have hq : CFSG.IsQuasisimple ↥L := hD.hyp.quasi
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  have hTM : T ≤ M := hD.hyp.sylow.1
  have hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  obtain ⟨-, hVcomm, -, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hC := d391_cent hD
  obtain ⟨-, ⟨t, htT, htn⟩, hsplitW, h5⟩ := h35 W M L T L V hD hlt hC
  obtain ⟨hsplit, hsumW⟩ := hsplitW t htT htn
  have hVT := orbSup_eq_sup htT hsplit
  set tM : ↥M := ⟨t, hTM htT⟩ with htM
  have hΛ := d391_Λ_normal hD
  have hirrQ := isIrr_tildeQ hD
  have hgenQ := iSup_smul_tildeQ hD
  have hdichQ := iso_or_iso_tildeQ hD hlt hC h5 htT (hTM htT) htn
  have hQsq : ∀ q : W ⧸ modFix L (⊤ : Subgroup W), q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hexp v, QuotientGroup.mk_one]
  have hsupQ := sup_isoSum_smul hΛ hgenQ hdichQ
  obtain ⟨k, hk1, -⟩ := count_isoSum hQsq hΛ hirrQ (A := (⊥ : Subgroup ↥M)) IsPGroup.of_bot
    (fun a ha => by rw [Subgroup.mem_bot.1 ha, one_smul])
  set π : W →* W ⧸ modFix L (⊤ : Subgroup W) := QuotientGroup.mk' (modFix L (⊤ : Subgroup W))
    with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w) := fun g w => rfl
  have hker : π.ker = fixV L := by
    rw [hπ, QuotientGroup.ker_mk']
    exact modFix_top_eq L
  have hVTmap : (orbSup T V).map π = tilde L ⊤ V ⊔ tM • tilde L ⊤ V := by
    rw [hVT, Subgroup.map_sup, smul_tildeQ hD.hyp.Mp_normal]
    rfl
  have hGV : L ⊔ T ≤ stabSub (orbSup T V) := (n1_sup_le_stabSub_sec hD.hyp).trans inf_le_left
  have hcommV : commV L = ⊤ := Z391.commV_eq_top hMn hVcomm hD.hyp.gen
  have hk2 : 2 ≤ k := by
    by_contra hk
    have hQ₁ : isoSum (L.subgroupOf M) (tilde L ⊤ V) = tilde L ⊤ V := by
      symm
      refine Subgroup.eq_of_le_of_card_ge self_le_isoSum ?_
      rw [card_eq_two_pow hQsq, card_eq_two_pow hQsq, hk1]
      exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have htopQ : (orbSup T V).map π = ⊤ := by
      rw [hVTmap, ← hsupQ, hQ₁]
    have h1 : orbSup T V ⊔ fixV L = ⊤ := by
      have h2 := congrArg (Subgroup.comap π) htopQ
      rwa [Subgroup.comap_map_eq, Subgroup.comap_top, hker] at h2
    apply htop
    rw [eq_top_iff, ← hcommV, commV_eq_commSub, ← h1, commSub_sup_fixV le_rfl]
    exact commSub_le_of_invariant fun x hx w hw =>
      (hGV ((le_sup_left : L ≤ L ⊔ T) hx) w).2 hw
  have hv3 : 3 ≤ rk ↥(tilde L ⊤ V) := by
    have hinj := (injective_twoClass_tildeQ hD h5).1
    have hperf : Group.IsPerfect ↥(L.subgroupOf M) := by
      have : Group.IsPerfect ↥L := hq.1
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hLM).symm.surjective
    have hnt : Nontrivial ↥(L.subgroupOf M) := by
      have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
      exact (Subgroup.subgroupOfEquivOfLe hLM).toEquiv.nontrivial
    exact three_le_rk_of_injective hQsq _ hinj
  obtain ⟨r, hr⟩ : ∃ r : ℚ, qhatOf M = (r : WithTop ℚ) := by
    have hne : qhatOf M ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hqM
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    exact ⟨r, hr.symm⟩
  have hr2 : r ≤ 2 := WithTop.coe_le_coe.mp (hr ▸ hqM)
  obtain ⟨A₁, hA₁⟩ := QhatStar_nonempty hr hr2
  have hA₁2 : IsPGroup 2 ↥A₁ := by
    obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA₁
    exact hA2.isElemAbelian2.isPGroup
  obtain ⟨x, hx, hA₁x⟩ := F7.isSylowTwoOf_exists_conj_le hD.hyp.sylow (QhatStar_le hA₁) hA₁2
  set A := conjBy x⁻¹ A₁ with hAdef
  have hAQ : A ∈ QhatStar M := conjBy_mem_QhatStar hA₁ (M.inv_mem hx)
  have hAT : A ≤ T := by
    intro y hy
    rw [mem_conjBy_iff, inv_inv] at hy
    have := hA₁x hy
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this
  obtain ⟨r', hr', -, ⟨⟨hA2, hAr'⟩, hA3⟩, -⟩ := QhatStar_spec hAQ
  have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr)
  rw [hrr] at hAr'
  have hAr : rAV A = r := hAr'
  obtain ⟨a, haA, ha1, haL⟩ := hunf A hA2 hAT hA3 (by rw [hAr]; exact hr2)
  have hB : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ≠ ⊥ := by
    intro h
    apply ha1
    have : a ∈ A ⊓ Subgroup.centralizer (L : Set (MulAut W)) :=
      ⟨haA, Subgroup.mem_centralizer_iff.2 fun l hl => (haL l hl).symm⟩
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  have hrkA : 2 ≤ rk ↥A := by
    set B := A ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hBdef
    have hBM : B ≤ M := inf_le_left.trans hA2.1
    have hBΛ : ∀ e ∈ B.subgroupOf M, ∀ l ∈ L.subgroupOf M, e * l = l * e := by
      intro e he l hl
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 he).2) _ hl).symm
    have hBnt : ∃ e ∈ B.subgroupOf M, ∃ q : W ⧸ modFix L (⊤ : Subgroup W), e • q ≠ q := by
      obtain ⟨b, hbB, hb1⟩ := (Subgroup.bot_or_exists_ne_one B).resolve_left hB
      refine ⟨⟨b, hBM hbB⟩, hbB, ?_⟩
      by_contra hcon
      push Not at hcon
      exact hb1 (d391_eq_one_of_fix hD (hBM hbB)
        (fun l hl => ((Subgroup.mem_centralizer_iff.1 hbB.2) l hl).symm) hcon)
    have h1 := rk_le_nB_of_comm hΛ hirrQ hgenQ hBΛ hBnt
    have h2 : nB (B.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) ≤
        nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) :=
      nB_anti (Subgroup.subgroupOf_mono M (inf_le_left : B ≤ A)) ⊤
    have h3 := Z391.nB_top_le_rkIdx_fixV π hπsurj hπM (A.subgroupOf M)
    rw [Subgroup.map_subgroupOf_eq_of_le hA2.1] at h3
    have hrA0 : 0 < rk ↥A := hA2.rk_pos
    have h4 : rkIdx (fixV A) ≤ 2 * rk ↥A := by
      have h := hAr.le.trans hr2
      unfold rAV at h
      have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA0
      rw [div_le_iff₀ hpos] at h
      exact_mod_cast h
    omega
  refine ⟨t, A, r, k, ⟨hD, hr, hr2, hlt, htop, hC, htT, htn, hsplit, hsumW, hVT, h5, hk1, hk2,
    hv3, hAQ, hAT, hAr, hB, hrkA, ?_, ?_, ?_⟩⟩
  · exact fun c hcT hc2 hcL => fix_orbSup_of_comm hD hlt hC htT htn hsplit hcT hc2 hcL
  · exact fun a haT haV => comm_of_fix hD hC haT haV
  · exact fun p hp hp5 => commutator_pCoreOf_eq_bot hexp hr hAQ hrkA hp hp5

namespace D310USit

variable {M T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  {A : Subgroup (MulAut W)} {r : ℚ} {k : ℕ} (hS : D310USit M T L V t A r k)
include hS

theorem exp : ∀ w : W, w ^ 2 = 1 := hS.hD.hyp.exp

theorem L_le : L ≤ M := le_of_mem_cComp hS.hD.hyp.comp

theorem T_le : T ≤ M := hS.hD.hyp.sylow.1

theorem t_mem : t ∈ M := hS.T_le hS.htT

theorem A_le : A ≤ M := QhatStar_le hS.hAQ

theorem M_le_normalizer : M ≤ Subgroup.normalizer (L : Set (MulAut W)) := hS.hD.hyp.Mp_normal

theorem T_le_normalizer : T ≤ Subgroup.normalizer (L : Set (MulAut W)) := d391_T_le hS.hD

theorem quasi : CFSG.IsQuasisimple ↥L := hS.hD.hyp.quasi

theorem perfect : ⁅L, L⁆ = L := by
  have : Group.IsPerfect ↥L := hS.quasi.1
  exact Subgroup.commutator_eq_self

theorem qsqtk : IsQuotientOfSQTKTC ↥M := hS.hD.hyp.qsqtk

theorem pCoreOf_two_eq_bot : CFSG.Open.pCoreOf 2 M = ⊥ := hS.hD.hyp.pCoreOf_eq_bot

theorem commV_eq_top : commV L = ⊤ := by
  obtain ⟨-, hVcomm, -, -⟩ := mem_irrPlus_top_iff.1 hS.hD.hyp.irr
  have hMn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hS.hD.hyp.Mp_normal hm)) l).1 hl
  exact Z391.commV_eq_top hMn hVcomm hS.hD.hyp.gen

theorem le_normalizer_cent :
    M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (L : Set (MulAut W)) : Subgroup _) :
      Set (MulAut W)) := by
  intro m hm
  have hconj : ∀ g ∈ M, ∀ c ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)),
      g * c * g⁻¹ ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
    intro g hg c hc
    refine ⟨M.mul_mem (M.mul_mem hg hc.1) (M.inv_mem hg),
      Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
    have hl' : g⁻¹ * l * g ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (hS.hD.hyp.Mp_normal (M.inv_mem hg)) l).1 hl
      rwa [inv_inv] at h1
    have h1 := (Subgroup.mem_centralizer_iff.1 hc.2) _ hl'
    calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * l := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => hconj m hm c hc, fun hc => ?_⟩
  have h1 := hconj m⁻¹ (M.inv_mem hm) _ hc
  simpa [mul_assoc] using h1

theorem pCoreOf_two_cent_eq_bot :
    CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer (L : Set (MulAut W))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
    (hS.le_normalizer_cent.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  rw [hS.pCoreOf_two_eq_bot] at h
  exact le_bot_iff.1 h

theorem pCoreOf_cent_le (p : ℕ) [Fact p.Prime] :
    CFSG.Open.pCoreOf p (M ⊓ Subgroup.centralizer (L : Set (MulAut W))) ≤
      CFSG.Open.pCoreOf p M :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
    ((CFSG.LieType.BorelTits.pCoreOf_le p _).trans inf_le_left)
    (hS.le_normalizer_cent.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup p _)

theorem le_centralizer_pCoreOf_cent {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    A ≤ Subgroup.centralizer
      (CFSG.Open.pCoreOf p (M ⊓ Subgroup.centralizer (L : Set (MulAut W))) : Set (MulAut W)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 := hS.hOp p hp hp5
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact (Subgroup.mem_centralizer_iff.1 (h1 (hS.pCoreOf_cent_le p hg)) a ha).symm

theorem cent_le_cent : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ≤
    M ⊓ Subgroup.centralizer (L : Set (MulAut W)) :=
  inf_le_inf_right _ hS.A_le

theorem isA2 : IsA2 M A := by
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hS.hAQ
  exact hA2

theorem isPGroup_cent : IsPGroup 2 ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W))) :=
  hS.isA2.isElemAbelian2.isPGroup.to_le inf_le_left

theorem rkIdx_le : rkIdx (fixV A) ≤ 2 * rk ↥A := by
  have hrA0 : 0 < rk ↥A := hS.isA2.rk_pos
  have h := hS.hAr.le.trans hS.hr2
  unfold rAV at h
  have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA0
  rw [div_le_iff₀ hpos] at h
  exact_mod_cast h

theorem fix_orbSup_iff {a : MulAut W} (ha : a ∈ A) :
    (∀ w ∈ orbSup T V, a w = w) ↔ ∀ l ∈ L, a * l = l * a := by
  refine ⟨fun h => hS.hTV a (hS.hAT ha) fun v hv => h v (le_orbSup T V hv), fun h =>
    hS.hCT a (hS.hAT ha) (hS.isA2.isElemAbelian2.2 a ha) h⟩

theorem quot_sq : ∀ q : W ⧸ modFix L (⊤ : Subgroup W), q ^ 2 = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H v => rw [← QuotientGroup.mk_pow, hS.exp v, QuotientGroup.mk_one]

theorem Λ_normal : ∀ g : ↥M, ∀ l ∈ L.subgroupOf M, g * l * g⁻¹ ∈ L.subgroupOf M :=
  d391_Λ_normal hS.hD

theorem irr :
    letI := qAct hS.hD.hyp.Mp_normal
    XMod.IsIrr ↥(L.subgroupOf M) (tilde L ⊤ V) := isIrr_tildeQ hS.hD

theorem gen :
    letI := qAct hS.hD.hyp.Mp_normal
    (⨆ g : ↥M, g • tilde L ⊤ V) = ⊤ := iSup_smul_tildeQ hS.hD

theorem not_iso :
    letI := qAct hS.hD.hyp.Mp_normal
    ¬ XMod.Iso ↥(L.subgroupOf M) ((⟨t, hS.t_mem⟩ : ↥M) • tilde L ⊤ V) (tilde L ⊤ V) :=
  not_iso_tildeQ hS.hD hS.hlt hS.hC hS.htT hS.t_mem hS.htn

theorem iso_or :
    letI := qAct hS.hD.hyp.Mp_normal
    ∀ g : ↥M, XMod.Iso ↥(L.subgroupOf M) (g • tilde L ⊤ V) (tilde L ⊤ V) ∨
      XMod.Iso ↥(L.subgroupOf M) (g • tilde L ⊤ V) ((⟨t, hS.t_mem⟩ : ↥M) • tilde L ⊤ V) :=
  iso_or_iso_tildeQ hS.hD hS.hlt hS.hC hS.h5 hS.htT hS.t_mem hS.htn

theorem sup_isoSum :
    letI := qAct hS.hD.hyp.Mp_normal
    isoSum (L.subgroupOf M) (tilde L ⊤ V) ⊔
      (⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V) = ⊤ := by
  let _i := qAct hS.hD.hyp.Mp_normal
  exact sup_isoSum_smul hS.Λ_normal hS.gen hS.iso_or

theorem inf_isoSum :
    letI := qAct hS.hD.hyp.Mp_normal
    isoSum (L.subgroupOf M) (tilde L ⊤ V) ⊓
      (⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V) = ⊥ := by
  let _i := qAct hS.hD.hyp.Mp_normal
  exact inf_isoSum_smul hS.Λ_normal hS.irr hS.not_iso

theorem rk_top :
    rk ↥(⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) = 2 * k * rk ↥(tilde L ⊤ V) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have h1 := rk_sup_add_rk_inf (isoSum (L.subgroupOf M) (tilde L ⊤ V))
    ((⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V))
  rw [hS.sup_isoSum, hS.inf_isoSum, rk_bot, rk_smul, hS.hk, add_zero] at h1
  rw [h1]
  ring

theorem faithful {x : MulAut W} (hxM : x ∈ M) (hxL : ∀ l ∈ L, x * l = l * x) :
    letI := qAct hS.hD.hyp.Mp_normal
    (∀ q : W ⧸ modFix L (⊤ : Subgroup W), (⟨x, hxM⟩ : ↥M) • q = q) → x = 1 :=
  d391_eq_one_of_fix hS.hD hxM hxL

theorem rk_le_of_isInv {S : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))}
    (hSinv : letI := qAct hS.hD.hyp.Mp_normal; XMod.IsInv ↥(L.subgroupOf M) S) (hne : S ≠ ⊥) :
    rk ↥(tilde L ⊤ V) ≤ rk ↥S := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have h1 := rk_dvd_of_isInv hS.quot_sq hS.Λ_normal hS.irr hS.gen hSinv
  have h2 : 0 < rk ↥S := by
    by_contra h0
    exact hne ((rk_eq_zero_iff hS.quot_sq).1 (by omega))
  exact Nat.le_of_dvd h2 h1

theorem nB_le_rkIdx {X : Subgroup (MulAut W)} (hXM : X ≤ M) :
    letI := qAct hS.hD.hyp.Mp_normal
    nB (X.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) ≤ rkIdx (fixV X) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have h := Z391.nB_top_le_rkIdx_fixV (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))
    (QuotientGroup.mk'_surjective _) (fun g w => rfl) (X.subgroupOf M)
  rwa [Subgroup.map_subgroupOf_eq_of_le hXM] at h

end D310USit

end CFSG.Quasithin.SmithD310U
