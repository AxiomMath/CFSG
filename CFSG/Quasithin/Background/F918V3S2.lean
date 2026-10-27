module

public import CFSG.Quasithin.Background.F918V2G3
public import CFSG.Quasithin.Background.A1cModuleSub

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem v3_commute_of_isPGroup_normal {N : Subgroup (MulAut W)} {q : ℕ} (hq : q.Prime)
    (hL : CFSG.IsQuasisimple ↥L) (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥)
    (hLM : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (hLle : L ≤ M)
    (hN : IsPGroup q N) (hNn : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) (hNle : N ≤ M) :
    ∀ n ∈ N, ∀ l ∈ L, n * l = l * n := by
  have hcomm_le : ⁅L, N⁆ ≤ L ⊓ N := by
    rw [Subgroup.commutator_le]
    intro l hl n hn
    refine ⟨?_, ?_⟩
    · have h1 : n * l⁻¹ * n⁻¹ ∈ L := hLM n (hNle hn) l⁻¹ (L.inv_mem hl)
      have := L.mul_mem hl h1
      simpa [commutatorElement_def, mul_assoc] using this
    · have h1 : l * n * l⁻¹ ∈ N := hNn l (hLle hl) n hn
      have := N.mul_mem h1 (N.inv_mem hn)
      simpa [commutatorElement_def, mul_assoc] using this
  have hJn : ((L ⊓ N).subgroupOf L).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hx.1) (L.inv_mem g.2), ?_⟩
    simpa using hNn (g : MulAut W) (hLle g.2) x hx.2
  have hcentral : ∀ c ∈ L ⊓ N, ∀ l ∈ L, c * l = l * c := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hL hJn with h | h
    · exfalso
      have hLN : L ≤ N := by
        intro x hx
        have : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ N).subgroupOf L := h ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).2
      have hLp : IsPGroup q ↥L := hN.to_le hLN
      have : Fact q.Prime := ⟨hq⟩
      have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL1
      have : Group.IsNilpotent ↥L := hLp.isNilpotent
      have : Group.IsPerfect ↥L := hL.1
      exact Group.IsPerfect.not_isSolvable ↥L inferInstance
    · intro c hc l hl
      have hcL : c ∈ L := hc.1
      have hmem : (⟨c, hcL⟩ : ↥L) ∈ (L ⊓ N).subgroupOf L := Subgroup.mem_subgroupOf.mpr hc
      have := Subgroup.mem_center_iff.mp (h hmem) ⟨l, hl⟩
      exact (congrArg Subtype.val this).symm
  have h1 : ⁅⁅L, N⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (hcentral c (hcomm_le hc) l hl).symm
  have h2 : ⁅⁅N, L⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm N L]; exact h1
  have h3 : ⁅⁅L, L⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hperf] at h3
  intro n hn l hl
  have h4 : ⁅l, n⁆ ∈ ⁅L, N⁆ := Subgroup.commutator_mem_commutator hl hn
  rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h4
  exact h4.symm

theorem v3_isIrrPlus_commV {X D : Subgroup (MulAut W)} {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hV : ∀ w : W, w ^ 2 = 1) (hD : D ∈ Xk X k) (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) :
    XMod.IsIrrPlus ↥D (commV D) := by
  obtain ⟨hdec, hinf⟩ := Xk_decomp hV hD
  have hinv : ∀ d ∈ D, ∀ u ∈ commV D, d u ∈ commV D := by
    intro d hd u hu
    induction hu using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨x, hx, v, rfl⟩ := hc
      refine Subgroup.subset_closure ⟨x, hx, d v, ?_⟩
      have h1 : d (x v) = x (d v) := by
        have := congrArg (fun φ : MulAut W => φ v) (hDab d hd x hx)
        simpa [MulAut.mul_apply] using this
      rw [map_mul, map_inv, h1]
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha
  have hIsInv : XMod.IsInv ↥D (commV D) := fun a u hu => hinv a a.2 u hu
  refine ⟨hIsInv, ?_, ?_⟩
  · apply le_antisymm
    · rw [XMod.commOf, Subgroup.closure_le]
      rintro _ ⟨a, l, hl, rfl⟩
      exact Subgroup.mul_mem _ (hIsInv a l hl) (Subgroup.inv_mem _ hl)
    · rw [commV, Subgroup.closure_le]
      rintro _ ⟨x, hx, v, rfl⟩
      have hv : v ∈ commV D ⊔ fixV D := by rw [hdec]; exact Subgroup.mem_top v
      obtain ⟨u₁, hu₁, c₀, hc₀, rfl⟩ := Subgroup.mem_sup.mp hv
      have hxc : x c₀ = c₀ := hc₀ x hx
      have e : x (u₁ * c₀) * (u₁ * c₀)⁻¹ = x u₁ * u₁⁻¹ := by
        rw [map_mul, hxc]; group
      rw [e]
      exact Subgroup.subset_closure ⟨⟨x, hx⟩, u₁, hu₁, rfl⟩
  · have hfix : XMod.fixed ↥D (commV D) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : x ∈ fixV D := fun g hg => hx.2 ⟨g, hg⟩
      have : x ∈ commV D ⊓ fixV D := ⟨hx.1, h1⟩
      rwa [hinf] at this
    rw [hfix]
    refine ⟨?_, fun J hJ hbot hJle => ?_⟩
    · refine bot_lt_iff_ne_bot.mpr fun h => ?_
      have : rk (commV D) = 2 * k := hD.2.2
      have h0 : rk (commV D) = 0 := by rw [h]; unfold rk; simp
      rcases hk with rfl | rfl <;> omega
    · by_cases hJ0 : J = ⊥
      · exact Or.inl hJ0
      · refine Or.inr (Xk_irreducible hV hk hD (fun g hg f hf => hJ ⟨g, hg⟩ f hf) hJle hJ0)

theorem v3_isTwoReduced_of_isPGroup {D : Subgroup (MulAut W)} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hDp : IsPGroup q D) (U : Subgroup W) : XMod.IsTwoReduced ↥D U := by
  intro D' _ hD' d hd l hl
  obtain ⟨k, hk⟩ := hD' d hd
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf).mp hDp d
  have hcop : Nat.Coprime (orderOf d) (2 ^ k) := by
    rw [ha]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  have hord : orderOf (d ^ 2 ^ k) = orderOf d := hcop.orderOf_pow
  have hle : Subgroup.zpowers (d ^ 2 ^ k) ≤ Subgroup.zpowers d :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) _)
  have heq : Subgroup.zpowers (d ^ 2 ^ k) = Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge hle (by simp only [Nat.card_zpowers, hord]; exact le_rfl)
  have hdz : d ∈ Subgroup.zpowers (d ^ 2 ^ k) := heq ▸ Subgroup.mem_zpowers d
  have hst : Subgroup.zpowers (d ^ 2 ^ k) ≤ MulAction.stabilizer (↥D) l :=
    Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hk l hl)
  have := hst hdz
  rwa [MulAction.mem_stabilizer_iff] at this

theorem v3_trivial_on_irrPlus {D L : Subgroup (MulAut W)} {U : Subgroup W} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hDp : IsPGroup q D) (hV : ∀ w : W, w ^ 2 = 1) (hU : XMod.IsIrrPlus ↥D U)
    (hperf : ⁅L, L⁆ = L) (hDL : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d)
    (hLU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) : ∀ l ∈ L, ∀ u ∈ U, l u = u := by
  have hO2 := v3_isTwoReduced_of_isPGroup hq hq2 hDp U
  have hcyc : IsCyclic ↥(XMod.aut ↥D U) := (XMod.isCyclic_aut_of_isIrrPlus hV hU hO2).1
  have hstab : ∀ l ∈ L, l ∈ stabSub U := by
    intro l hl u
    refine ⟨fun h => ?_, fun h => hLU l hl u h⟩
    have := hLU l⁻¹ (L.inv_mem hl) _ h
    simpa using this
  have haut : ∀ (l : MulAut W) (hl : l ∈ L), resHom U ⟨l, hstab l hl⟩ ∈ XMod.aut ↥D U := by
    intro l hl
    rw [XMod.mem_aut_iff]
    intro a u u'
    have hcomm : ∀ w : W, (a : MulAut W) (l w) = l ((a : MulAut W) w) := fun w => by
      have := congrArg (fun φ : MulAut W => φ w) (hDL a a.2 l hl)
      simpa [MulAut.mul_apply] using this
    have e1 : ((resHom U ⟨l, hstab l hl⟩ u : ↥U) : W) = l (u : W) := rfl
    have e2 : ((resHom U ⟨l, hstab l hl⟩ u' : ↥U) : W) = l (u' : W) := rfl
    rw [e1, e2]
    show (a : MulAut W) (u : W) = (u' : W) ↔ (a : MulAut W) (l (u : W)) = l (u' : W)
    rw [hcomm]
    exact ⟨fun h => by rw [h], fun h => l.injective h⟩
  have hcomm_triv : ∀ l₁ ∈ L, ∀ l₂ ∈ L, ∀ u ∈ U, l₁ (l₂ u) = l₂ (l₁ u) := by
    intro l₁ hl₁ l₂ hl₂ u hu
    let _ : CommGroup ↥(XMod.aut ↥D U) := IsCyclic.commGroup
    have h := congrArg (fun φ : ↥(XMod.aut ↥D U) => ((φ.1 ⟨u, hu⟩ : ↥U) : W))
      (mul_comm (⟨_, haut l₁ hl₁⟩ : ↥(XMod.aut ↥D U)) ⟨_, haut l₂ hl₂⟩)
    exact h
  have hP : ∀ g ∈ ⁅L, L⁆, ∀ u ∈ U, g u = u := by
    intro g hg
    rw [Subgroup.commutator_def] at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := hg
      intro u hu
      have hw : l₁⁻¹ (l₂⁻¹ u) ∈ U := hLU _ (L.inv_mem hl₁) _ (hLU _ (L.inv_mem hl₂) _ hu)
      have h := hcomm_triv l₁ hl₁ l₂ hl₂ _ hw
      have e : ⁅l₁, l₂⁆ u = l₁ (l₂ (l₁⁻¹ (l₂⁻¹ u))) := by
        simp [commutatorElement_def, MulAut.mul_apply]
      rw [e, h]
      simp
    | one => intro u _; rfl
    | mul a b _ _ ha hb => intro u hu; rw [MulAut.mul_apply, hb u hu, ha u hu]
    | inv a _ ha =>
      intro u hu
      have := ha u hu
      calc a⁻¹ u = a⁻¹ (a u) := by rw [this]
        _ = u := by simp
  intro l hl
  exact hP l (by rw [hperf]; exact hl)

theorem d392_centralizes_pCore (hD : D3Std M L T L V) {A : Subgroup (MulAut W)}
    (hA : A ∈ QhatStar M) {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) :
    ∀ a ∈ A, ∀ x ∈ pCoreOf q M, a * x = x * a := by
  have hV : ∀ w : W, w ^ 2 = 1 := hD.hyp.exp
  by_cases hq2 : q = 2
  · intro a _ x hx
    have hbot := D31.pCoreOf_eq_bot hD.hyp
    rw [hq2, hbot, Subgroup.mem_bot] at hx
    rw [hx]
    simp
  · have : Fact q.Prime := ⟨hq⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨a, haA, x, hxP, hne⟩ := hcon
    obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, -⟩ := QhatStar_spec hA
    have hAM : A ≤ M := hA2.le
    have hDne : ⁅pCoreOf q M, A⁆ ≠ ⊥ := commutator_ne_bot_iff.mpr ⟨x, hxP, a, haA, hne⟩
    obtain ⟨h35, h5, -⟩ := D2_13 hV hr hA hq2 rfl hDne
    have hq5 : q = 5 := h35.resolve_left hq3
    obtain ⟨-, -, hcard, hcyc, -, hrk⟩ := h5 hq5
    set D : Subgroup (MulAut W) := ⁅pCoreOf q M, A⁆ with hDD
    have hPn : ∀ m ∈ M, ∀ g ∈ pCoreOf q M, m * g * m⁻¹ ∈ pCoreOf q M := fun m hm g hg =>
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf q M hm) g).mp hg
    have hPM : pCoreOf q M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le q M
    have hPp : IsPGroup q (pCoreOf q M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup q M
    have hDP : D ≤ pCoreOf q M := by
      rw [hDD, Subgroup.commutator_le]
      intro y hy a' ha'
      have h1 := hPn a' (hAM ha') y⁻¹ (Subgroup.inv_mem _ hy)
      have h2 := (pCoreOf q M).mul_mem hy h1
      simpa [commutatorElement_def, mul_assoc] using h2
    have hDM : D ≤ M := hDP.trans hPM
    have hDfit : D ≤ fittingOf M := hDP.trans (le_fittingOf_of_normal hPM hPp hPn)
    have hDX : D ∈ Xk M 2 := ⟨hDfit, by rw [hcard], by rw [hrk]⟩
    have hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
      intro x hx y hy
      let _ : CommGroup ↥D := IsCyclic.commGroup
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥D) ⟨y, hy⟩)
    have hU : XMod.IsIrrPlus ↥D (commV D) := v3_isIrrPlus_commV (Or.inr rfl) hV hDX hDab
    have hDp : IsPGroup q D := hPp.to_le hDP
    have hperf : ⁅L, L⁆ = L := hD.hyp.comp.2.1
    have hL1 : L ≠ ⊥ := hD.hyp.comp.1
    have hLle : L ≤ M := le_of_mem_cComp hD.hyp.comp
    have hLM : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
      ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
    have hDL : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d := fun d hd l hl =>
      v3_commute_of_isPGroup_normal hq hD.hyp.quasi hperf hL1 hLM hLle hPp hPn hPM d (hDP hd) l hl
    have hLU : ∀ l ∈ L, ∀ u ∈ commV D, l u ∈ commV D := by
      intro l hl u hu
      induction hu using Subgroup.closure_induction with
      | mem c hc =>
        obtain ⟨x, hx, v, rfl⟩ := hc
        refine Subgroup.subset_closure ⟨x, hx, l v, ?_⟩
        have h1 : l (x v) = x (l v) := by
          have := congrArg (fun φ : MulAut W => φ v) (hDL x hx l hl)
          simpa [MulAut.mul_apply] using this.symm
        rw [map_mul, map_inv, h1]
      | one => rw [map_one]; exact Subgroup.one_mem _
      | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
      | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha
    have htriv := v3_trivial_on_irrPlus hq hq2 hDp hV hU hperf hDL hLU
    apply hDne
    rw [Subgroup.eq_bot_iff_forall]
    intro d hd
    refine Z391.v2g_faithful_on_Q hD (hDM hd) (fun l hl => hDL d hd l hl) fun w => ?_
    intro l hl
    exact htriv l hl _ (Subgroup.subset_closure ⟨d, hd, w, rfl⟩)

end CFSG.Quasithin
