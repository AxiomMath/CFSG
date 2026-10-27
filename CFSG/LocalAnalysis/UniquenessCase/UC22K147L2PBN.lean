module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2PCore
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair

open Subgroup CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.QuasithinUnique.Setup.X7b CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Br
open CFSG.RankThree.GF2n.Tim81.Sec2 (IsOrthModule)
open scoped MatrixGroups

theorem mul_self_apply_rootSub {F K : Type} [Field F] [CharP F 2] [Group K]
    (ι : ↥(rootSub F) →* K) (u : ↥(rootSub F)) : ι u * ι u = 1 := by
  rw [← map_mul, show u * u = 1 from Subtype.ext (mul_self_of_mem_rootSub u.2), map_one]

theorem nontrivial_rootSub {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) : Nontrivial ↥(rootSub F) := by
  classical
  exact Finite.one_lt_card_iff_nontrivial.mp
    (by rw [natCard_rootSub, hF]; exact Nat.one_lt_two_pow (by omega))

section Rep

variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem mem_ker_sub_one {r : G} {v : V} : v ∈ LinearMap.ker (ρ r - 1) ↔ ρ r v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem exists_moved_of_fixSub_eq_bot {K : Subgroup G} (h : fixSub ρ K = ⊥)
    {Y : Submodule (ZMod 2) V} (hY0 : Y ≠ ⊥) : ∃ k ∈ K, ∃ y ∈ Y, ρ k y ≠ y := by
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  by_contra hc
  push Not at hc
  apply hy0
  have : y ∈ fixSub ρ K := fun k hk => hc k hk y hy
  rwa [h, Submodule.mem_bot] at this

theorem exists_moved_of_ne_one {K : Subgroup G} [IsSimpleGroup ↥K] {Y : Submodule (ZMod 2) V}
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ K Y) (hmov : ∃ k ∈ K, ∃ y ∈ Y, ρ k y ≠ y) {k : G} (hk : k ∈ K)
    (hk1 : k ≠ 1) : ∃ y ∈ Y, ρ k y ≠ y := by
  by_contra hc
  push Not at hc
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (restr ρ hY).ker with h | h
  · apply hk1
    have : (⟨k, hk⟩ : ↥K) ∈ (restr ρ hY).ker :=
      MonoidHom.mem_ker.mpr (LinearMap.ext fun y => Subtype.ext (hc y y.2))
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  · obtain ⟨k', hk', y, hy, hne⟩ := hmov
    apply hne
    have : (⟨k', hk'⟩ : ↥K) ∈ (restr ρ hY).ker := by
      rw [h]
      exact Subgroup.mem_top _
    exact congrArg Subtype.val (LinearMap.congr_fun (MonoidHom.mem_ker.mp this) ⟨y, hy⟩)

theorem apply_sub_self {r : G} (hr : r * r = 1) (v : V) : ρ r (ρ r v - v) = ρ r v - v := by
  rw [map_sub, ← Module.End.mul_apply, ← map_mul, hr, map_one, Module.End.one_apply,
    ZModModule.sub_eq_add, ZModModule.sub_eq_add, add_comm]

theorem apply_comm {x y : G} (h : x * y = y * x) (v : V) : ρ x (ρ y v) = ρ y (ρ x v) := by
  show (ρ x * ρ y) v = (ρ y * ρ x) v
  rw [← map_mul ρ x y, h, map_mul]

theorem false_of_irreducible {L : Subgroup G} {M : Submodule (ZMod 2) V}
    (hML : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L M) (hirr : ∀ C ≤ M, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C → C = ⊥ ∨ C = M) {r : G}
    (hr : r * r = 1) (hrM : ∀ m ∈ M, ρ r m ∈ M) (hrL : ∀ l ∈ L, l * r = r * l)
    (hmov : ∃ m ∈ M, ρ r m ≠ m) : False := by
  have hB : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (M.map (ρ r - 1)) := by
    rintro l hl _ ⟨m, hm, rfl⟩
    refine ⟨ρ l m, hML l hl m hm, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, apply_comm (hrL l hl)]
  have hBM : M.map (ρ r - 1) ≤ M := by
    rintro _ ⟨m, hm, rfl⟩
    exact sub_mem (hrM m hm) hm
  obtain ⟨m, hm, hne⟩ := hmov
  have hB0 : M.map (ρ r - 1) ≠ ⊥ := fun h => hne (by
    have : (ρ r - 1) m ∈ M.map (ρ r - 1) := ⟨m, hm, rfl⟩
    rwa [h, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this)
  rcases hirr _ hBM hB with h | h
  · exact hB0 h
  · have hm' : m ∈ M.map (ρ r - 1) := by
      rw [h]
      exact hm
    obtain ⟨m', -, hm'⟩ := hm'
    simp only [LinearMap.sub_apply, Module.End.one_apply] at hm'
    rw [← hm'] at hne
    exact hne (apply_sub_self hr m')

end Rep

section Split

variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {ρ : Representation (ZMod 2) G V}

theorem false_of_split {L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : ↥L ≃* SL(2, F)) {s : ℕ} (hs1 : 1 ≤ s) {hs : Fintype.card F = 2 ^ (2 * s)}
    {M : Submodule (ZMod 2) V} (hML : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L M)
    (hall : ∀ D ≤ M, ∀ hD : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L D, D ≠ ⊥ → D ≠ M →
      (∀ E ≤ D, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L E → E = ⊥ ∨ E = D) ∧
        IsOrthModule hs ((restr ρ hD).comp e.symm.toMonoidHom))
    {U C : Submodule (ZMod 2) V} (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L U) (hC : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C)
    (hUC : U ⊔ C = M) (hinf : U ⊓ C = ⊥) (hU0 : U ≠ ⊥) (hC0 : C ≠ ⊥)
    (ι : ↥(rootSub F) →* G) (hιL : ∀ u, ∀ l ∈ L, l * ι u = ι u * l)
    (hιM : ∀ u, ∀ m ∈ M, ρ (ι u) m ∈ M) (hιmov : ∀ u, u ≠ 1 → ∃ m ∈ M, ρ (ι u) m ≠ m) :
    False := by
  classical
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hR : Nat.card ↥(rootSub F) = 2 ^ (2 * s) := natCard_rootSub.trans hs
  have hRp : IsPGroup 2 ↥(rootSub F) := IsPGroup.of_card hR
  haveI := nontrivial_rootSub (by omega) hs
  obtain ⟨u₀, hu₀⟩ := exists_ne (1 : ↥(rootSub F))
  have hM0 : M ≠ ⊥ := fun h => hU0 (eq_bot_iff.mpr ((le_sup_left.trans hUC.le).trans h.le))
  let P : Submodule (ZMod 2) V := M ⊓ fixSub (ρ.comp ι) ⊤
  have hPL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L P := fun l hl v hv => ⟨hML l hl v hv.1, fun u _ => by
    have hvu : ρ (ι u) v = v := hv.2 u (mem_top u)
    show ρ (ι u) (ρ l v) = ρ l v
    rw [← apply_comm (hιL u l hl), hvu]⟩
  have hPM : P ≤ M := inf_le_left
  have hP0 : P ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
    obtain ⟨w, hw0, hw, hwM⟩ :=
      CFSG.QuasithinUnique.Setup.X7.exists_fixed_ne_zero_of_pGroup (ZMod 2) Nat.prime_two hRp
        (ρ.comp ι) hv0
    have hwP : w ∈ P := ⟨Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hιM g v hv) hwM,
      fun u _ => hw u⟩
    exact fun h => hw0 (by rwa [h, Submodule.mem_bot] at hwP)
  have hCP : ∀ u, u ≠ 1 → ∀ v ∈ M, ρ (ι u) v = v → v ∈ P := by
    intro u hu
    have hCL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (M ⊓ LinearMap.ker (ρ (ι u) - 1)) := fun l hl v hv =>
      ⟨hML l hl v hv.1, mem_ker_sub_one.mpr (by
        rw [← apply_comm (hιL u l hl), mem_ker_sub_one.mp hv.2])⟩
    have hPC : P ≤ M ⊓ LinearMap.ker (ρ (ι u) - 1) := fun v hv =>
      ⟨hv.1, mem_ker_sub_one.mpr (hv.2 u (mem_top u))⟩
    have hCM : M ⊓ LinearMap.ker (ρ (ι u) - 1) ≠ M := fun h => by
      obtain ⟨m, hm, hne⟩ := hιmov u hu
      rw [← h] at hm
      exact hne (mem_ker_sub_one.mp hm.2)
    obtain ⟨hirrC, -⟩ := hall _ inf_le_left hCL
      (fun h => hP0 (eq_bot_iff.mpr (hPC.trans h.le))) hCM
    rcases hirrC P hPC hPL with h | h
    · exact absurd h hP0
    · intro v hv hvu
      rw [h]
      exact ⟨hv, mem_ker_sub_one.mpr hvu⟩
  have hPM' : P ≠ M := fun h => by
    obtain ⟨m, hm, hne⟩ := hιmov u₀ hu₀
    rw [← h] at hm
    exact hne (hm.2 u₀ (mem_top u₀))
  obtain ⟨hPirr, hPo⟩ := hall P hPM hPL hP0 hPM'
  obtain ⟨W, hWM, hWL, hW0, hWP⟩ : ∃ W ≤ M, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L W ∧ W ≠ ⊥ ∧ W ⊓ P = ⊥ := by
    by_cases h : U ⊓ P = ⊥
    · exact ⟨U, le_sup_left.trans hUC.le, hU, hU0, h⟩
    · refine ⟨C, le_sup_right.trans hUC.le, hC, hC0, ?_⟩
      rcases hPirr (P ⊓ U) inf_le_left (fun l hl v hv => ⟨hPL l hl v hv.1, hU l hl v hv.2⟩)
        with h' | h'
      · exact absurd ((inf_comm U P).trans h') h
      · rw [eq_bot_iff, ← hinf]
        exact le_inf (fun v hv => (h'.ge hv.2).2) inf_le_left
  let ι₁ : ↥(rootSub F) →* G := L.subtype.comp (e.symm.toMonoidHom.comp (rootSub F).subtype)
  obtain ⟨w₀, hw₀W, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨x, hx0, hxA, hxW⟩ :=
    CFSG.QuasithinUnique.Setup.X7.exists_fixed_ne_zero_of_pGroup (ZMod 2) Nat.prime_two hRp
      (ρ.comp ι₁) hw₀
  have hxW' : x ∈ W := Submodule.span_le.mpr
    (by rintro _ ⟨g, rfl⟩; exact hWL _ (e.symm g).2 w₀ hw₀W) hxW
  have hxM : x ∈ M := hWM hxW'
  have hxP : x ∉ P := fun h => hx0 (by
    have : x ∈ W ⊓ P := ⟨hxW', h⟩
    rwa [hWP, Submodule.mem_bot] at this)
  have hφP : ∀ u, ρ (ι u) x - x ∈ P := fun u => by
    by_cases hu : u = 1
    · rw [hu, map_one, map_one, Module.End.one_apply, sub_self]
      exact zero_mem _
    · exact hCP u hu _ (sub_mem (hιM u x hxM) hxM) (apply_sub_self (mul_self_apply_rootSub ι u) x)
  have hφA : ∀ u, ∀ a ∈ rootSub F,
      ρ ((e.symm a : ↥L) : G) (ρ (ι u) x - x) = ρ (ι u) x - x := by
    intro u a ha
    have hxa : ρ ((e.symm a : ↥L) : G) x = x := hxA ⟨a, ha⟩
    rw [map_sub, apply_comm (hιL u _ (e.symm a).2), hxa]
  let φ : ↥(rootSub F) → ↥(CFSG.QuasithinUnique.Setup.X7.fixedSub
      ((restr ρ hPL).comp e.symm.toMonoidHom) (rootSub F)) :=
    fun u => ⟨⟨ρ (ι u) x - x, hφP u⟩, fun a ha => Subtype.ext (hφA u a ha)⟩
  have hφ : Function.Injective φ := by
    intro u u' h
    have h0 : ρ (ι u) x - x = ρ (ι u') x - x := congrArg Subtype.val (congrArg Subtype.val h)
    have h1 : ρ (ι u) x = ρ (ι u') x := sub_left_injective h0
    by_contra hne
    have hv : u'⁻¹ * u ≠ 1 := fun h' => hne (inv_mul_eq_one.mp h').symm
    refine hxP (hCP _ hv x hxM ?_)
    rw [map_mul, map_inv, map_mul, Module.End.mul_apply, h1, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  have hT := CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule.card_fixedSub (hF := hs) hPo
    (rootSub F) (fun a ha => mul_self_of_mem_rootSub ha) hR
  have hle := (Nat.card_le_card_of_injective φ hφ).trans_eq hT
  rw [hR] at hle
  exact absurd hle (not_le.mpr (pow_lt_pow_right₀ (by norm_num) (by omega)))

end Split

theorem IsPair.not_mem_normalizer_of_fixSub_eq_bot {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible) {L L₂ : Subgroup G} (hP : IsPair L L₂)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (e : ↥L ≃* SL(2, F)) {n : ℕ} (hn : 3 ≤ n)
    (hF : Fintype.card F = 2 ^ n) {t : G} (ht : t * t = 1) (ht1 : t ≠ 1)
    (htd : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) ≤ n + 1)
    (hB : fixSub ρ L₂ = ⊥) : t ∉ normalizer (L : Set G) := by
  intro htN
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have h4 : 4 ≤ Nat.card F := by
    rw [hFn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : IsSimpleGroup SL(2, F) := P22y.isSimpleGroup_sl2 h4
  haveI : IsSimpleGroup ↥L := e.isSimpleGroup
  obtain ⟨e₂'⟩ := hP.nonempty_mulEquiv
  let e₂ : ↥L₂ ≃* SL(2, F) := e₂'.trans e
  haveI : IsSimpleGroup ↥L₂ := e₂.isSimpleGroup
  haveI := nontrivial_rootSub (by omega) hF
  haveI := hP.sup_normal
  have hBL := hP.fixSub_eq_bot hB
  have hfix : fixSub ρ L ⊓ fixSub ρ L₂ = ⊥ := by rw [hB, inf_bot_eq]
  have hρt : ρ t ≠ 1 := fun h => ht1 (hρ (h.trans (map_one ρ).symm))
  obtain ⟨M, hM, -⟩ := exists_isMinInv_moved hirr hP.sup_normal hρt
  have hML : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L M := fun l hl => hM.1 l (mem_sup_left hl)
  have hML₂ : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L₂ M := fun l hl => hM.1 l (mem_sup_right hl)
  have hMt : ∀ m ∈ M, ρ t m ∈ M := fun m hm =>
    hP.apply_mem_of_isMinInv e (by omega) hFn hfix hM ht htd hm
  have hMH : IsMinInv ρ (L ⊔ L₂ ⊔ zpowers t) M :=
    ⟨fun h hh m hm => invariant_of_incL_tElt (L ⊔ L₂) t ht
        (ρ.comp (L ⊔ L₂ ⊔ zpowers t).subtype) M (fun l u hu => hM.1 l l.2 u hu) hMt ⟨h, hh⟩ m hm,
      hM.2.1, fun D hDM hD hD0 => hM.2.2 D hDM (fun x hx => hD x (mem_sup_left hx)) hD0⟩
  let ι : ↥(rootSub F) →* G := L₂.subtype.comp (e₂.symm.toMonoidHom.comp (rootSub F).subtype)
  have hιL : ∀ u, ∀ l ∈ L, l * ι u = ι u * l := fun u l hl => hP.commute hl (e₂.symm u).2
  have hιM : ∀ u, ∀ m ∈ M, ρ (ι u) m ∈ M := fun u => hML₂ _ (e₂.symm u).2
  have hιmov : ∀ u, u ≠ 1 → ∃ m ∈ M, ρ (ι u) m ≠ m := fun u hu =>
    exists_moved_of_ne_one hML₂ (exists_moved_of_fixSub_eq_bot hB hM.2.1) (e₂.symm u).2
      fun h => hu (by
        have h1 : e₂.symm (u : SL(2, F)) = 1 := Subtype.ext h
        exact Subtype.ext (by simpa using congrArg e₂ h1))
  have hl₀ : ∃ l ∈ L, t * l ≠ l * t := by
    by_contra hc
    push Not at hc
    obtain ⟨Y, hY, hY0, hYd⟩ := exists_le_disp_of_commute ρ hρ ht1 (L := L) hc
    have := two_mul_le_finrank_of_moves ρ e (by omega) hFn hY
      (exists_moved_of_fixSub_eq_bot hBL hY0)
    omega
  rcases nat_or_orth_or_eight_or_split_sub ρ (H := L ⊔ L₂ ⊔ zpowers t)
      (le_sup_left.trans le_sup_left)
      (sup_le (sup_le Subgroup.le_normalizer hP.symm.le_normalizer) (zpowers_le.mpr htN)) hMH hML
      (exists_moved_of_fixSub_eq_bot hBL hM.2.1) e hn hF (mem_sup_right (mem_zpowers t)) ht hl₀
      htd with
    ⟨hirrM, -⟩ | ⟨s, hs, hsF, hall, U, C, hU, hC, hUC, hinf, hU0, hC0⟩
  · obtain ⟨u₀, hu₀⟩ := exists_ne (1 : ↥(rootSub F))
    exact false_of_irreducible hML hirrM (mul_self_apply_rootSub ι u₀) (hιM u₀) (hιL u₀)
      (hιmov u₀ hu₀)
  · exact false_of_split e (by omega) hML hall hU hC hUC hinf hU0 hC0 ι hιL hιM hιmov

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair
