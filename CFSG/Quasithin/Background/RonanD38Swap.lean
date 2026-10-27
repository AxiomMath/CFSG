module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34D38Pair

public section

namespace CFSG.Quasithin.RonanD38

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W]

theorem two_mul_rk_lt_rkIdx_of_swap {V V' CV : Subgroup W} (hsum : V ⊔ V' = ⊤)
    (hD : V ⊓ V' ≤ CV) {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A)
    (hperm : ∀ a ∈ A, (a ∈ stabSub V ∧ a ∈ stabSub V') ∨
      (V.map a.toMonoidHom = V' ∧ V'.map a.toMonoidHom = V))
    {a : MulAut W} (haA : a ∈ A) (haV : a ∉ stabSub V) (hV3 : 3 + rk ↥CV ≤ rk ↥V)
    (hSB : ∀ B ≤ A, B ≤ stabSub V → commSub V B ≠ ⊥ →
      2 * rk ↥(autSub B V) ≤ rk ↥V - rk ↥(B5.fixSec B V CV)) :
    2 * rk ↥A < rkIdx (fixV A) := by
  have hidx := rk_add_rkIdx (fixV A)
  have htop := H13.rk_top_add_rk_inf hsum
  have hdec : ∀ w : W, ∃ v ∈ V, ∃ v' ∈ V', v * v' = w := fun w =>
    Subgroup.mem_sup.mp (hsum ▸ Subgroup.mem_top w)
  have hcent : ∀ g : MulAut W, g ∈ centSub V → g ∈ centSub V' → g = 1 := by
    intro g hg hg'
    ext w
    obtain ⟨v, hv, v', hv', rfl⟩ := hdec w
    rw [map_mul, hg v hv, hg' v' hv', MulAut.one_apply]
  have hrkAut : ∀ {B : Subgroup (MulAut W)} {Y : Subgroup W}, B ≤ stabSub Y →
      rk ↥(autSub B Y) + rk ↥(B ⊓ centSub Y) = rk ↥B := by
    intro B Y hBY
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', card_autSub_mul hBY]
  obtain ⟨hVa, hV'a⟩ : V.map a.toMonoidHom = V' ∧ V'.map a.toMonoidHom = V := by
    rcases hperm a haA with ⟨h, -⟩ | h
    · exact absurd h haV
    · exact h
  set A₀ := A ⊓ stabSub V with hA₀
  have ha2 : a * a = 1 := by rw [← sq]; exact hA.2 a haA
  have hcomm : ∀ g ∈ A₀, g * a = a * g := fun g hg => hA.1 g hg.1 a haA
  have hstab : A₀ ≤ stabSub V := inf_le_right
  have hsum' : V ⊔ V.map a.toMonoidHom = ⊤ := by rw [hVa]; exact hsum
  have hswap := rk_fixV_swap_le ha2 hcomm hstab hsum'
  rw [hVa] at hswap
  have hfixA : fixV A ≤ fixV A₀ ⊓ fixV (Subgroup.zpowers a) :=
    le_inf (fixV_anti inf_le_left) (fixV_anti (Subgroup.zpowers_le.mpr haA))
  have hidx2 : (A₀.subgroupOf A).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haA⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : MulAut W) ∈ stabSub V
    · have hbA₀ : (b : MulAut W) ∈ A₀ := ⟨b.2, hb⟩
      refine Or.inr ⟨hbA₀, fun hba => haV ?_⟩
      have := (stabSub V).mul_mem ((stabSub V).inv_mem hb) hba.2
      simpa using this
    · refine Or.inl ⟨⟨A.mul_mem b.2 haA, ?_⟩, fun hbA₀ => hb hbA₀.2⟩
      apply H13.mem_stabSub_of_map_eq'
      have e : ((b : MulAut W) * a).toMonoidHom =
          (b : MulAut W).toMonoidHom.comp a.toMonoidHom := MonoidHom.ext fun x => rfl
      rw [e, ← Subgroup.map_map, hVa]
      rcases hperm b b.2 with ⟨h, -⟩ | ⟨-, hb2⟩
      · exact absurd h hb
      · exact hb2
  have hcardA : Nat.card ↥A = 2 * Nat.card ↥A₀ := by
    have h1 := (A₀.subgroupOf A).card_mul_index
    rw [hidx2] at h1
    have h2 : Nat.card ↥(A₀.subgroupOf A) = Nat.card ↥A₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h2] at h1
    omega
  have hrkA : rk ↥A = rk ↥A₀ + 1 := by
    unfold rk
    rw [hcardA, padicValNat.mul (by norm_num) Nat.card_pos.ne', padicValNat_self, add_comm]
  have hA₀f : A₀ ⊓ centSub V = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨⟨hgA, hgs⟩, hgV⟩
    rw [Subgroup.mem_bot]
    refine hcent g hgV fun v' hv' => ?_
    have hv'a : a v' ∈ V := by
      rw [← hV'a]
      exact ⟨v', hv', rfl⟩
    have hga : g * a = a * g := hcomm g ⟨hgA, hgs⟩
    have h1 : g (a v') = a (g v') := by
      have := congrArg (fun φ : MulAut W => φ v') hga
      simpa [MulAut.mul_apply] using this
    have h2 : a (g v') = a v' := by rw [← h1, hgV _ hv'a]
    exact a.injective h2
  have hr := hrkAut hstab
  rw [hA₀f, rk_bot, add_zero] at hr
  have hUU : commModSub V A₀ (V ⊓ V') ≤ B5.fixSec A₀ V CV := fun u hu =>
    ⟨hu.1, fun g hg => hD (hu.2 g hg)⟩
  have h1 := rk_mono hUU
  have h2 := rk_mono hfixA
  have h4 : rk ↥(V ⊓ V') ≤ rk ↥CV := rk_mono hD
  have h5 : rk ↥V' = rk ↥V := by rw [← hVa, rk_map_aut_eq]
  have h6 : rk ↥(B5.fixSec A₀ V CV) ≤ rk ↥V := rk_mono (B5.fixSec_le _ _ _)
  have h9 : rk ↥((V ⊓ V') ⊓ fixV A₀) ≤ rk ↥(V ⊓ V') := rk_mono inf_le_left
  by_cases hne : commSub V A₀ = ⊥
  · have h8 : rk ↥(commModSub V A₀ (V ⊓ V')) ≤ rk ↥V := rk_mono (commModSub_le _ _ _)
    have hA₀b : A₀ = ⊥ := by
      rw [eq_bot_iff, ← hA₀f]
      intro g hg
      exact ⟨hg, fun v hv => (commSub_eq_bot_iff.mp hne) hv g hg⟩
    have hrk0 : rk ↥A₀ = 0 := by rw [hA₀b, rk_bot]
    omega
  · have hb2 := hSB A₀ inf_le_left hstab hne
    omega

end CFSG.Quasithin.RonanD38
