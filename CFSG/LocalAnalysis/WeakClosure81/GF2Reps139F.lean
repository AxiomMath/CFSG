module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Basic
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139B
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139C
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139D
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Cliff
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundB

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private theorem w1369_commutator_eq_self_of_isQuasisimple {B : Type*} [Group B]
    {K : Subgroup B} (hq : CFSG.Open.IsQuasisimple K) : ⁅K, K⁆ = K := by
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  exact Subgroup.commutator_eq_self

private abbrev w1369_phiHom (b : MulAut W) : W →* W :=
  MonoidHom.mk' (fun w => b w * w⁻¹) (by
    intro x y
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
    ac_rfl)

private theorem w1369_zpowers_stabilizes {U : Subgroup W} {g : MulAut W}
    (hg2 : g * g = 1) (hg : ∀ u ∈ U, g u ∈ U) :
    ∀ x ∈ Subgroup.zpowers g, ∀ u ∈ U, x u ∈ U := by
  have hgU : g ∈ stabSub U := by
    rw [mem_stabSub]
    intro v
    constructor
    · intro hv
      have hgg : g (g v) = v := by
        have := congrArg (fun f : MulAut W => f v) hg2
        simpa [MulAut.mul_apply] using this
      rw [← hgg]
      exact hg (g v) hv
    · exact hg v
  have hle : Subgroup.zpowers g ≤ stabSub U := Subgroup.zpowers_le.mpr hgU
  intro x hx u hu
  exact (mem_stabSub.mp (hle hx) u).2 hu

private theorem w1369_commSub_le_of_compl {C C' : Subgroup W} {K : Subgroup (MulAut W)}
    (hC : C ≤ fixV K) (hC'K : StableUnder K C') (hsup : C ⊔ C' = ⊤) :
    commSub ⊤ K ≤ C' := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨k, hk, w, -, rfl⟩
  have hw' : w ∈ C ⊔ C' := by rw [hsup]; exact Subgroup.mem_top w
  obtain ⟨c, hc, c', hc', hcc'⟩ := Subgroup.mem_sup.mp hw'
  rw [← hcc']
  have hkc : k c * c⁻¹ = 1 := by rw [mem_fixV.mp (hC hc) k hk, mul_inv_cancel]
  have hsplit : k (c * c') * (c * c')⁻¹ = (k c * c⁻¹) * (k c' * c'⁻¹) := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl
  rw [hsplit, hkc, one_mul]
  exact C'.mul_mem (hC'K k hk c' hc') (C'.inv_mem hc')

private theorem w1369_axis_le_of_minimal (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)}
    (hC : DNormComp G D) (hK : IsComponentOf K G) (hKperf : ⁅K, K⁆ = K)
    (hKX : ∀ k ∈ K, ∀ x ∈ X, k * x = x * k) (hfixX : fixV X = ⊥)
    (hfixKU : fixV K ⊓ commSub ⊤ K = ⊥) {M : Subgroup W} (hMU : M ≤ commSub ⊤ K)
    (hM0 : M ≠ ⊥) (hMK : StableUnder K M) (hMX : StableUnder X M)
    (hmin : ∀ N, N ≤ M → N ≠ ⊥ → StableUnder K N → StableUnder X N → N = M)
    {e : MulAut W} (he : e ∈ D) (he1 : e ≠ 1) (hKe : ⁅K, Subgroup.zpowers e⁆ = K) :
    commSub ⊤ (Subgroup.zpowers e) ≤ M := by
  have he2 : e * e = 1 := by rw [← pow_two]; exact S.elem.2 e he
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have heK : K.map (MulAut.conj e).toMonoidHom = K := hC K hK e he
  have hconj_mem : ∀ k ∈ K, MulAut.conj e k ∈ K := by
    intro k hk
    have h := Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom hk
    rwa [heK] at h
  have heMe : StableUnder K (M.map e.toMonoidHom) := by
    intro k hk u hu
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hu
    refine Subgroup.mem_map.mpr ⟨MulAut.conj e⁻¹ k m, hMK _ ?_ m hm, ?_⟩
    · rw [show MulAut.conj e⁻¹ k = MulAut.conj e k from by rw [heinv]]
      exact hconj_mem k hk
    · rw [MulAut.conj_apply]
      simp
  have heMX : StableUnder X (M.map e.toMonoidHom) := by
    intro x hx u hu
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hu
    refine Subgroup.mem_map.mpr ⟨x m, hMX x hx m hm, ?_⟩
    have hcomm : x * e = e * x := (S.DX e he x hx).symm
    calc e (x m) = (e * x) m := rfl
      _ = (x * e) m := by rw [hcomm]
      _ = x (e m) := rfl
  have hMinter_of_ne : M.map e.toMonoidHom ≠ M → M ⊓ M.map e.toMonoidHom = ⊥ := by
    intro hneM
    by_contra hne_bot
    have hstab : StableUnder K (M ⊓ M.map e.toMonoidHom) :=
      fun k hk n hn => ⟨hMK k hk n hn.1, heMe k hk n hn.2⟩
    have hstabX : StableUnder X (M ⊓ M.map e.toMonoidHom) :=
      fun x hx n hn => ⟨hMX x hx n hn.1, heMX x hx n hn.2⟩
    have hEq : M ⊓ M.map e.toMonoidHom = M := hmin _ inf_le_left hne_bot hstab hstabX
    have hle : M ≤ M.map e.toMonoidHom := inf_eq_left.mp hEq
    have hcard : Nat.card ↥(M.map e.toMonoidHom) = Nat.card M :=
      Subgroup.card_map_of_injective e.injective
    exact hneM (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])).symm
  have hMeq : M.map e.toMonoidHom = M := by
    by_contra hneM
    have hMinter : M ⊓ M.map e.toMonoidHom = ⊥ := hMinter_of_ne hneM
    have hφinj : Function.Injective (fun m : M => e m * m⁻¹) := by
      intro m₁ m₂ h
      have h1 : w1369_phiHom e ((m₁ * m₂⁻¹ : M) : W) = 1 := by
        have hthis : w1369_phiHom e (m₁ : W) = w1369_phiHom e (m₂ : W) := h
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hthis, mul_inv_cancel]
      have h2 : e ((m₁ * m₂⁻¹ : M) : W) = ((m₁ * m₂⁻¹ : M) : W) :=
        mul_inv_eq_one.mp h1
      have hmem : ((m₁ * m₂⁻¹ : M) : W) ∈ M.map e.toMonoidHom :=
        ⟨(m₁ * m₂⁻¹ : M), (m₁ * m₂⁻¹ : M).2, h2⟩
      have hbot : ((m₁ * m₂⁻¹ : M) : W) ∈ (⊥ : Subgroup W) := by
        rw [← hMinter]
        exact ⟨(m₁ * m₂⁻¹ : M).2, hmem⟩
      have h3 : ((m₁ * m₂⁻¹ : M) : W) = 1 := Subgroup.mem_bot.mp hbot
      exact Subtype.ext (mul_inv_eq_one.mp h3)
    have hrkM_le : rk ↥M ≤ 2 := by
      let ψ : M → ↥(commSub ⊤ (Subgroup.zpowers e)) := fun m =>
        ⟨e m * m⁻¹, Subgroup.subset_closure
          ⟨e, Subgroup.mem_zpowers e, (m : W), Subgroup.mem_top _, rfl⟩⟩
      have hψ : Function.Injective ψ := by
        intro m₁ m₂ h
        exact hφinj (congrArg Subtype.val h)
      have hcard := Nat.card_le_card_of_injective ψ hψ
      rw [card_eq_two_pow hw2 M,
        card_eq_two_pow hw2 (commSub ⊤ (Subgroup.zpowers e))] at hcard
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
      rwa [(Std139.commSub_axis hw2 S he he1).1] at this
    have h2le : 2 ≤ rk ↥M := xstable_two_le_rk hw2 hfixX hMX hM0
    have hrkM : rk ↥M = 2 := by omega
    have hMXirr : IsIrrOn X M (M ⊓ fixV X) := by
      rw [hfixX, inf_bot_eq]
      refine ⟨bot_lt_iff_ne_bot.mpr hM0, hMX, ?_, ?_⟩
      · intro x hx u hu
        rw [Subgroup.mem_bot] at hu ⊢
        rw [hu, map_one]
      · intro J hJ _ hJM
        rcases eq_or_ne J ⊥ with rfl | hJne
        · exact Or.inl rfl
        · right
          have h2 : 2 ≤ rk ↥J := xstable_two_le_rk hw2 hfixX hJ hJne
          have hle : rk ↥J ≤ rk ↥M := rk_mono hJM
          exact eq_of_le_of_rk_le hw2 hJM (by omega)
    have hXK : ⁅X, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact hKX k hk x hx
    have hschur := s13_schur_perfect (W := W) (fun w => by rw [← pow_two]; exact hw2 w) X K
      hXK hKperf M hMX hMK hMXirr
    rw [hfixX, inf_bot_eq] at hschur
    have hMlefix : M ≤ fixV K := commSub_eq_bot_iff.mp (le_bot_iff.mp hschur)
    have hMbot : M = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have h1 : m ∈ fixV K ⊓ commSub ⊤ K := ⟨hMlefix hm, hMU hm⟩
      rwa [hfixKU] at h1
    exact hM0 hMbot
  have hMe_stab : ∀ m ∈ M, e m ∈ M := by
    intro m hm
    have : e m ∈ M.map e.toMonoidHom := ⟨m, hm, rfl⟩
    rwa [hMeq] at this
  have hMnontriv : commSub M (Subgroup.zpowers e) ≠ ⊥ := by
    intro hbot
    have hMfix : M ≤ fixV (Subgroup.zpowers e) := commSub_eq_bot_iff.mp hbot
    have htriv : ∀ m ∈ M, e m = m := fun m hm => mem_fixV_zpowers_iff.mp (hMfix hm)
    have he_cent : e ∈ centSub M := mem_centSub.mpr htriv
    have hzle : Subgroup.zpowers e ≤ centSub M := Subgroup.zpowers_le.mpr he_cent
    have hle : ⁅K, Subgroup.zpowers e⁆ ≤ centSub M := by
      rw [Subgroup.commutator_le]
      intro k hk y hy
      rw [mem_centSub]
      intro u hu
      have hyu : y u = u := mem_centSub.mp (hzle hy) u hu
      have hyinv : y⁻¹ u = u := mem_centSub.mp ((centSub M).inv_mem (hzle hy)) u hu
      have hku : k⁻¹ u ∈ M := hMK k⁻¹ (K.inv_mem hk) u hu
      have hyku : y (k⁻¹ u) = k⁻¹ u := mem_centSub.mp (hzle hy) (k⁻¹ u) hku
      rw [commutatorElement_def]
      simp only [MulAut.mul_apply]
      rw [hyinv, hyku, MulAut.apply_inv_self]
    rw [hKe] at hle
    have hMlefix : M ≤ fixV K := by
      intro m hm
      rw [mem_fixV]
      intro k hk
      exact mem_centSub.mp (hle hk) m hm
    have hMbot : M = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have h1 : m ∈ fixV K ⊓ commSub ⊤ K := ⟨hMlefix hm, hMU hm⟩
      rwa [hfixKU] at h1
    exact hM0 hMbot
  have hMXstable : StableUnder X (commSub M (Subgroup.zpowers e)) := by
    have hcomm : ∀ y ∈ Subgroup.zpowers e, ∀ b ∈ X, y * b = b * y := by
      intro y hy b hb
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (show Commute e b from S.DX e he b hb) j).eq
    exact CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := Subgroup.zpowers e) (B := X)
      (M := M) hcomm hMX
  have hrkMe : 2 ≤ rk ↥(commSub M (Subgroup.zpowers e)) :=
    xstable_two_le_rk hw2 hfixX hMXstable hMnontriv
  have hrkWe : rk ↥(commSub ⊤ (Subgroup.zpowers e)) = 2 := (Std139.commSub_axis hw2 S he he1).1
  have heq : commSub M (Subgroup.zpowers e) = commSub ⊤ (Subgroup.zpowers e) :=
    eq_of_le_of_rk_le hw2 (commSub_mono le_top le_rfl) (by rw [hrkWe]; exact hrkMe)
  have hMe_le_M : commSub M (Subgroup.zpowers e) ≤ M :=
    commSub_le_of_invariant (w1369_zpowers_stabilizes he2 hMe_stab)
  rw [← heq]
  exact hMe_le_M

private theorem w1369_axis_le_of_KX (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)}
    (hC : DNormComp G D) (hK : IsComponentOf K G) (hKperf : ⁅K, K⁆ = K)
    (hKX : ∀ k ∈ K, ∀ x ∈ X, k * x = x * k) (hfixX : fixV X = ⊥)
    (hfixKU : fixV K ⊓ commSub ⊤ K = ⊥) {e : MulAut W} (he : e ∈ D) (he1 : e ≠ 1)
    (hKe : ⁅K, Subgroup.zpowers e⁆ = K) :
    ∀ C : Subgroup W, C ≤ commSub ⊤ K → C ≠ ⊥ → StableUnder K C → StableUnder X C →
      commSub ⊤ (Subgroup.zpowers e) ≤ C := by
  have key : ∀ r : ℕ, ∀ C : Subgroup W, rk ↥C = r → C ≤ commSub ⊤ K → C ≠ ⊥ →
      StableUnder K C → StableUnder X C → commSub ⊤ (Subgroup.zpowers e) ≤ C := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro C hr hCU hC0 hCK hCX
      by_cases hmin : ∀ N, N ≤ C → N ≠ ⊥ → StableUnder K N → StableUnder X N → N = C
      · exact w1369_axis_le_of_minimal hw2 S hC hK hKperf hKX hfixX hfixKU hCU hC0 hCK hCX
          hmin he he1 hKe
      · obtain ⟨N, hN⟩ := not_forall.mp hmin
        obtain ⟨hNC, hN'⟩ := not_imp.mp hN
        obtain ⟨hN0, hN''⟩ := not_imp.mp hN'
        obtain ⟨hNK, hN'''⟩ := not_imp.mp hN''
        obtain ⟨hNX, hNCne⟩ := not_imp.mp hN'''
        have hle : rk ↥N ≤ r := by rw [← hr]; exact rk_mono hNC
        have hne : rk ↥N ≠ r := by
          intro heq
          exact hNCne (eq_of_le_of_rk_le hw2 hNC (by rw [heq, hr]))
        exact (ih (rk ↥N) (by omega) N rfl (hNC.trans hCU) hN0 hNK hNX).trans hNC
  intro C hCU hC0 hCK hCX
  exact key (rk ↥C) C rfl hCU hC0 hCK hCX

theorem Std139.lemmaF (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n) (hn : 3 ≤ n)
    (hC : DNormComp G D) {K : Subgroup (MulAut W)} (hK : IsComponentOf K G)
    (hKD : ¬ K ≤ Subgroup.centralizer (D : Set (MulAut W))) :
    fixV K ⊔ commSub ⊤ K = ⊤ ∧ fixV K ⊓ commSub ⊤ K = ⊥ ∧ fixV K ≤ Y ∧
      (∀ e ∈ D, e ≠ 1 → commSub ⊤ (Subgroup.zpowers e) ≤ commSub ⊤ K ⊓ Y) ∧
      KXIrr K X (commSub ⊤ K) := by
  classical
  have hKperf : ⁅K, K⁆ = K := w1369_commutator_eq_self_of_isQuasisimple hK.2.2
  have hKX : ∀ k ∈ K, ∀ x ∈ X, k * x = x * k := Std139.component_commutes_X S hK
  have hKne : K ≠ ⊥ := by
    intro hbot
    exact hKD (by rw [hbot]; exact bot_le)
  have hKU : StableUnder K (commSub ⊤ K) :=
    CFSG.Quasithin.B1.commSub_invariant_of_normalizes (Y := K) (Bg := K) (M := ⊤)
      (fun b hb y hy => K.mul_mem (K.mul_mem hb hy) (K.inv_mem hb))
      (fun _ _ m _ => Subgroup.mem_top m)
  have hUX : StableUnder X (commSub ⊤ K) :=
    CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := K) (B := X) (M := ⊤)
      (fun y hy b hb => hKX y hy b hb) (fun _ _ m _ => Subgroup.mem_top m)
  obtain ⟨x, hxgen, hx3, hxne, hfixX, hsx⟩ := Std139.exists_gen hw2 S
  have hCK : StableUnder K (fixV K) := by
    intro k hk c hc
    rw [mem_fixV] at hc ⊢
    intro k' hk'
    rw [hc k hk, hc k' hk']
  have hCX : StableUnder X (fixV K) := by
    intro x hx c hc
    rw [mem_fixV] at hc ⊢
    intro k hk
    rw [← MulAut.mul_apply, hKX k hk x hx, MulAut.mul_apply, hc k hk]
  obtain ⟨C', hC'K, hC'X, hC'sup, hC'inf⟩ :=
    Std139.complete_reducibility_KX hw2 S hK hCK hCX
  have hUleC' : commSub ⊤ K ≤ C' := w1369_commSub_le_of_compl le_rfl hC'K hC'sup
  have hfix_inf : fixV K ⊓ commSub ⊤ K = ⊥ := by
    apply le_bot_iff.mp
    exact (inf_le_inf_left (fixV K) hUleC').trans (le_of_eq hC'inf)
  have hB_K : StableUnder K (fixV K ⊔ commSub ⊤ K) := by
    intro k hk w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    have hka : k a = a := mem_fixV.mp ha k hk
    rw [map_mul, hka]
    exact Subgroup.mem_sup.mpr ⟨a, ha, k b, hKU k hk b hb, rfl⟩
  have hB_X : StableUnder X (fixV K ⊔ commSub ⊤ K) := by
    intro x hx w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
    rw [map_mul]
    exact Subgroup.mem_sup.mpr ⟨x a, hCX x hx a ha, x b, hUX x hx b hb, rfl⟩
  obtain ⟨C'', hC''K, hC''X, hC''sup, hC''inf⟩ :=
    Std139.complete_reducibility_KX hw2 S hK hB_K hB_X
  have hKC'' : commSub C'' K = ⊥ := by
    have h1 : commSub C'' K ≤ commSub ⊤ K := commSub_mono le_top le_rfl
    have h2 : commSub C'' K ≤ C'' := commSub_le_of_invariant hC''K
    have h3 : commSub C'' K ≤ (fixV K ⊔ commSub ⊤ K) ⊓ C'' :=
      le_inf (h1.trans le_sup_right) h2
    rw [hC''inf] at h3
    exact le_bot_iff.mp h3
  have hC''leC : C'' ≤ fixV K := commSub_eq_bot_iff.mp hKC''
  have hC''bot : C'' = ⊥ := by
    have h : C'' ≤ (fixV K ⊔ commSub ⊤ K) ⊓ C'' := le_inf (hC''leC.trans le_sup_left) le_rfl
    rw [hC''inf] at h
    exact le_bot_iff.mp h
  have hfix_sup : fixV K ⊔ commSub ⊤ K = ⊤ := by
    have h : (fixV K ⊔ commSub ⊤ K) ⊔ C'' = fixV K ⊔ commSub ⊤ K := by
      rw [hC''bot, sup_bot_eq]
    rw [hC''sup] at h
    exact h.symm
  have hKe_of : ∀ e : MulAut W, e ∈ D → e ≠ 1 → ⁅K, Subgroup.zpowers e⁆ = K := by
    intro e he he1
    have hne : ⁅K, Subgroup.zpowers e⁆ ≠ ⊥ := by
      intro hbot
      have hle : K ≤ Subgroup.centralizer (Subgroup.zpowers e : Set (MulAut W)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      have hmem : ∀ k ∈ K, e * k = k * e := by
        intro k hk
        exact Subgroup.mem_centralizer_iff.mp (hle hk) e (Subgroup.mem_zpowers e)
      exact he1 ((Std139.lemmaD hw2 S hn hC hK hKD).2 e he hmem)
    exact comm_eq_self_of_component hK (hC K hK e he) hne
  have hpart4 : ∀ e ∈ D, e ≠ 1 → commSub ⊤ (Subgroup.zpowers e) ≤ commSub ⊤ K ⊓ Y := by
    intro e he he1
    have hB := Std139.lemmaB hw2 S he he1 hKX hKperf hKne (hC K hK e he) (hKe_of e he he1)
    exact le_inf hB.2 (Std139.commSub_axis hw2 S he he1).2.1
  have hCY : fixV K ≤ Y := by
    have hDgt : 1 < Nat.card D := by
      rw [S.Dcard]
      have h2 : 2 ≤ n - 1 := by omega
      calc 1 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) h2
    have hDne : D ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hDgt
      omega
    obtain ⟨⟨e, heD⟩, he1sub⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
    have he1 : e ≠ 1 := fun h => he1sub (Subtype.ext h)
    have he2 : e * e = 1 := by rw [← pow_two]; exact S.elem.2 e heD
    have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
    have hCe : ∀ c ∈ fixV K, e c ∈ fixV K := by
      intro c hc
      rw [mem_fixV] at hc ⊢
      intro k hk
      have hconj : e⁻¹ * k * e ∈ K := by
        have h1 : MulAut.conj e k ∈ K := by
          have h := Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom hk
          rwa [hC K hK e heD] at h
        rwa [show e⁻¹ * k * e = MulAut.conj e k from by rw [MulAut.conj_apply, heinv]]
      calc k (e c) = (k * e) c := rfl
        _ = (e * (e⁻¹ * k * e)) c := by
              rw [show k * e = e * (e⁻¹ * k * e) from by group]
        _ = e ((e⁻¹ * k * e) c) := rfl
        _ = e c := by rw [hc _ hconj]
    have hzstab : ∀ y ∈ Subgroup.zpowers e, ∀ c ∈ fixV K, y c ∈ fixV K :=
      w1369_zpowers_stabilizes he2 hCe
    have hcommCe : commSub (fixV K) (Subgroup.zpowers e) ≤ fixV K :=
      commSub_le_of_invariant hzstab
    have hcommCeU : commSub (fixV K) (Subgroup.zpowers e) ≤ commSub ⊤ K :=
      (commSub_mono le_top le_rfl).trans ((hpart4 e heD he1).trans inf_le_left)
    have hbot : commSub (fixV K) (Subgroup.zpowers e) = ⊥ := by
      have h := le_inf hcommCe hcommCeU
      rw [hfix_inf] at h
      exact le_bot_iff.mp h
    exact (commSub_eq_bot_iff.mp hbot).trans (le_of_eq (Std139.fixV_eq_axis hw2 S heD he1))
  have hU0 : commSub ⊤ K ≠ ⊥ := by
    intro hbot
    have htop : fixV K = ⊤ := top_le_iff.mp (commSub_eq_bot_iff.mp hbot)
    have hKbot : K = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro k hk
      ext w
      have hw : w ∈ fixV K := by rw [htop]; exact Subgroup.mem_top w
      simpa using mem_fixV.mp hw k hk
    exact hKne hKbot
  have hirr : ∀ C : Subgroup W, StableUnder K C → StableUnder X C → C ≤ commSub ⊤ K →
      C = ⊥ ∨ C = commSub ⊤ K := by
    intro C hCK hCX hCU
    by_cases hC0 : C = ⊥
    · exact Or.inl hC0
    · right
      by_contra hCU'
      have hDgt : 1 < Nat.card D := by
        rw [S.Dcard]
        have h2 : 2 ≤ n - 1 := by omega
        calc 1 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) h2
      have hDne : D ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hDgt
        omega
      obtain ⟨⟨e, heD⟩, he1sub⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
      have he1 : e ≠ 1 := fun h => he1sub (Subtype.ext h)
      have hKe := hKe_of e heD he1
      obtain ⟨C', hC'K, hC'X, hC'sup, hC'inf⟩ :=
        Std139.complete_reducibility_KX hw2 S hK hCK hCX
      let N : Subgroup W := commSub ⊤ K ⊓ C'
      have hNK : StableUnder K N := fun k hk nn hn => ⟨hKU k hk nn hn.1, hC'K k hk nn hn.2⟩
      have hNX : StableUnder X N := fun x hx nn hn => ⟨hUX x hx nn hn.1, hC'X x hx nn hn.2⟩
      have hNleU : N ≤ commSub ⊤ K := inf_le_left
      have hUeq : commSub ⊤ K = C ⊔ N := by
        apply le_antisymm
        · intro u hu
          have hu' : u ∈ C ⊔ C' := by rw [hC'sup]; exact Subgroup.mem_top u
          obtain ⟨c, hc, c', hc', hcc'⟩ := Subgroup.mem_sup.mp hu'
          rw [← hcc']
          have hcU : c ∈ commSub ⊤ K := hCU hc
          have hc'U : c' ∈ commSub ⊤ K := by
            have : c' = c⁻¹ * (c * c') := by group
            rw [this]
            exact (commSub ⊤ K).mul_mem ((commSub ⊤ K).inv_mem hcU) (hcc' ▸ hu)
          exact Subgroup.mem_sup.mpr ⟨c, hc, c', ⟨hc'U, hc'⟩, rfl⟩
        · exact sup_le hCU inf_le_left
      have hN0 : N ≠ ⊥ := by
        intro hNbot
        exact hCU' (by rw [hUeq, hNbot, sup_bot_eq])
      have haxisC : commSub ⊤ (Subgroup.zpowers e) ≤ C :=
        w1369_axis_le_of_KX hw2 S hC hK hKperf hKX hfixX hfix_inf heD he1 hKe
          C hCU hC0 hCK hCX
      have haxisN : commSub ⊤ (Subgroup.zpowers e) ≤ N :=
        w1369_axis_le_of_KX hw2 S hC hK hKperf hKX hfixX hfix_inf heD he1 hKe
          N hNleU hN0 hNK hNX
      have hCN : C ⊓ N = ⊥ := by
        change C ⊓ (commSub ⊤ K ⊓ C') = ⊥
        rw [← inf_assoc, inf_eq_left.mpr hCU, hC'inf]
      have hbot : commSub ⊤ (Subgroup.zpowers e) = ⊥ := by
        have h := le_inf haxisC haxisN
        rw [hCN] at h
        exact le_bot_iff.mp h
      have hrk : rk ↥(commSub ⊤ (Subgroup.zpowers e)) = 2 :=
        (Std139.commSub_axis hw2 S heD he1).1
      rw [hbot, rk_bot] at hrk
      omega
  exact ⟨hfix_sup, hfix_inf, hCY, hpart4, ⟨hU0, hKU, hUX, hirr⟩⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
