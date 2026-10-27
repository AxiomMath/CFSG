module

public import CFSG.Quasithin.Background.SimsG46ImprimPerm
import CFSG.Quasithin.Background.SimsG46ImprimFin4
import CFSG.Quasithin.Background.SimsG4Core
import CFSG.Quasithin.Background.SimsG45Transv

public section

namespace CFSG.Quasithin.SimsG4

namespace G46Imprim

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

structure IsTranspOn {r : ℕ} (W : Fin r → Submodule F V) (d : V ≃ₗ[F] V) (p q : Fin r) :
    Prop where
  ne : p ≠ q
  map_left : ∀ x ∈ W p, d x ∈ W q
  map_right : ∀ x ∈ W q, d x ∈ W p
  fix : ∀ t, t ≠ p → t ≠ q → ∀ x ∈ W t, d x = x

section Transp

variable {r : ℕ} {W : Fin r → Submodule F V} {G₀ : Subgroup (V ≃ₗ[F] V)} {d : V ≃ₗ[F] V}
  {p q : Fin r}

theorem IsTranspOn.symm (h : IsTranspOn W d p q) : IsTranspOn W d q p :=
  ⟨h.ne.symm, h.map_right, h.map_left, fun t htq htp => h.fix t htp htq⟩

theorem IsTranspOn.conj (hW : Function.Injective W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) {h : V ≃ₗ[F] V} (hh : h ∈ G₀)
    (hd : IsTranspOn W d p q) :
    IsTranspOn W (h * d * h⁻¹) (sumPerm W h p) (sumPerm W h q) := by
  have hinv := G₀.inv_mem hh
  have back : ∀ {i : Fin r} {x : V}, x ∈ W (sumPerm W h i) → h⁻¹ x ∈ W i := by
    intro i x hx
    have h1 := apply_mem_sumPerm hmap hinv hx
    rwa [sumPerm_inv_sumPerm hW hmap hh] at h1
  refine ⟨fun e => hd.ne (sumPerm_injective hW hmap hh e), fun x hx => ?_, fun x hx => ?_,
    fun t htp htq x hx => ?_⟩
  · simpa only [LinearEquiv.mul_apply] using
      apply_mem_sumPerm hmap hh (hd.map_left _ (back hx))
  · simpa only [LinearEquiv.mul_apply] using
      apply_mem_sumPerm hmap hh (hd.map_right _ (back hx))
  · have h1 : h⁻¹ x ∈ W (sumPerm W h⁻¹ t) := apply_mem_sumPerm hmap hinv hx
    have hne1 : sumPerm W h⁻¹ t ≠ p := fun e =>
      htp (by rw [← e, sumPerm_sumPerm_inv hW hmap hh])
    have hne2 : sumPerm W h⁻¹ t ≠ q := fun e =>
      htq (by rw [← e, sumPerm_sumPerm_inv hW hmap hh])
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hd.fix _ hne1 hne2 _ h1, mul_inv_apply]

theorem IsTranspOn.sumPerm_left (hne : ∀ i, W i ≠ ⊥) (hind : iSupIndep W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) (hdG : d ∈ G₀)
    (hd : IsTranspOn W d p q) : sumPerm W d p = q :=
  sumPerm_eq_of_mapsTo hne hind hmap hdG hd.map_left

theorem IsTranspOn.sumPerm_right (hne : ∀ i, W i ≠ ⊥) (hind : iSupIndep W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) (hdG : d ∈ G₀)
    (hd : IsTranspOn W d p q) : sumPerm W d q = p :=
  sumPerm_eq_of_mapsTo hne hind hmap hdG hd.map_right

theorem IsTranspOn.sumPerm_fix (hne : ∀ i, W i ≠ ⊥) (hind : iSupIndep W)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) (hdG : d ∈ G₀)
    (hd : IsTranspOn W d p q) {t : Fin r} (htp : t ≠ p) (htq : t ≠ q) : sumPerm W d t = t :=
  sumPerm_eq_of_mapsTo hne hind hmap hdG fun x hx => by
    rw [hd.fix t htp htq x hx]
    exact hx

theorem IsTranspOn.blocks (hd : IsTranspOn W d p q) {p' q' : Fin r} (h1 : p' ≠ p) (h2 : p' ≠ q)
    (h3 : q' ≠ p) (h4 : q' ≠ q) :
    (∀ x ∈ W p ⊔ W q, d x ∈ W p ⊔ W q) ∧ ∀ x ∈ W p' ⊔ W q', d x = x := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (hd.map_left y hy))
      (Submodule.mem_sup_left (hd.map_right z hz))
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hd.fix p' h1 h2 y hy, hd.fix q' h3 h4 z hz]

end Transp

theorem forall_of_iSup_eq_top {r : ℕ} {W : Fin r → Submodule F V} (htop : (⨆ i, W i) = ⊤)
    {P : V → Prop} (hmem : ∀ i, ∀ x ∈ W i, P x) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (v : V) : P v :=
  Submodule.iSup_induction (motive := P) W (by rw [htop]; exact Submodule.mem_top) hmem h0 hadd

theorem bilin_symm [CharP F 2] (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0) (x y : V) :
    B y x = B x y := by
  rw [SimsG45.bilin_skew B halt y x, CharTwo.neg_eq]

section Lines

variable {W : Fin 4 → Submodule F V} {w : Fin 4 → V} {G₀ : Subgroup (V ≃ₗ[F] V)}

theorem eq_zero_of_bilin_lines (B : LinearMap.BilinForm F V)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (htop : (⨆ i, W i) = ⊤) (hwW : ∀ i, W i = F ∙ w i)
    {x : V} (hx : ∀ t, B x (w t) = 0) : x = 0 := by
  refine hnd x fun y => forall_of_iSup_eq_top htop (P := fun y => B x y = 0)
    (fun i y hy => ?_) (map_zero _) (fun y z hy hz => ?_) y
  · rw [hwW] at hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    show B x (c • w i) = 0
    rw [map_smul, hx, smul_zero]
  · have hy' : B x y = 0 := hy
    have hz' : B x z = 0 := hz
    show B x (y + z) = 0
    rw [map_add, hy', hz', add_zero]

theorem eq_of_lines (htop : (⨆ i, W i) = ⊤) (hwW : ∀ i, W i = F ∙ w i) {g h : V ≃ₗ[F] V}
    (hgh : ∀ t, g (w t) = h (w t)) : g = h := by
  apply LinearEquiv.ext
  intro v
  refine forall_of_iSup_eq_top htop (P := fun v => g v = h v) (fun i y hy => ?_) (by simp)
    (fun y z hy hz => ?_) v
  · rw [hwW] at hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    show g (c • w i) = h (c • w i)
    rw [map_smul, map_smul, hgh]
  · have hy' : g y = h y := hy
    have hz' : g z = h z := hz
    show g (y + z) = h (y + z)
    rw [map_add, map_add, hy', hz']

theorem exists_transpOn [CharP F 2] (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hSp : G₀ ≤ spGroup B) (hne : ∀ i, W i ≠ ⊥)
    (hind : iSupIndep W) (htop : (⨆ i, W i) = ⊤)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) (hwW : ∀ i, W i = F ∙ w i)
    {d : V ≃ₗ[F] V} (hd : d ∈ transvSet G₀) : ∃ p q, IsTranspOn W d p q := by
  have hWinj := summand_injective hne hind
  obtain ⟨u, hu, c, hc, hform, -⟩ := SimsG45.exists_transv_form B halt hnd d (hSp hd.1) hd.2.1
  have hσσ : ∀ t, sumPerm W d (sumPerm W d t) = t := fun t => by
    rw [← sumPerm_mul hWinj hmap hd.1 hd.1, transv_mul_self d hd.2, sumPerm_one hWinj hmap]
  have hwmem : ∀ t, w t ∈ W t := fun t => by
    rw [hwW]
    exact Submodule.mem_span_singleton_self _
  have hfixed : ∀ t, B (w t) u = 0 → d (w t) = w t := fun t ht => by
    rw [hform, ht, mul_zero, zero_smul, add_zero]
  have hmoved : ∀ t, B (w t) u ≠ 0 → sumPerm W d t ≠ t ∧ u ∈ W t ⊔ W (sumPerm W d t) := by
    intro t ht
    obtain ⟨μ, hμ⟩ : ∃ μ : F, μ • w (sumPerm W d t) = d (w t) := by
      have h1 := apply_mem_sumPerm hmap hd.1 (hwmem t)
      rw [hwW] at h1
      exact Submodule.mem_span_singleton.mp h1
    have hcoef : c * B (w t) u ≠ 0 := mul_ne_zero hc ht
    have hu_eq : u = (c * B (w t) u)⁻¹ • (μ • w (sumPerm W d t) - w t) := by
      rw [hμ, hform (w t), add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hcoef, one_smul]
    refine ⟨fun hfix => ht ?_, ?_⟩
    · rw [hfix] at hu_eq
      rw [hu_eq]
      simp only [map_smul, map_sub, halt, smul_zero, sub_zero]
    · rw [hu_eq]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_right ?_)
        (Submodule.mem_sup_left (hwmem t)))
      exact Submodule.smul_mem _ _ (hwmem _)
  obtain ⟨p, hp⟩ : ∃ p, B (w p) u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu (eq_zero_of_bilin_lines B hnd htop hwW fun t => by rw [bilin_symm B halt, hcon t])
  obtain ⟨hpmov, hupq⟩ := hmoved p hp
  refine ⟨p, sumPerm W d p, Ne.symm hpmov, fun x hx => apply_mem_sumPerm hmap hd.1 hx,
    fun x hx => ?_, fun t htp htq x hx => ?_⟩
  · have h1 := apply_mem_sumPerm hmap hd.1 hx
    rwa [hσσ] at h1
  · have ht : B (w t) u = 0 := by
      by_contra ht
      obtain ⟨-, hut⟩ := hmoved t ht
      have h1 : sumPerm W d t ≠ p := fun e => htq (by rw [← e, hσσ])
      have h2 : sumPerm W d t ≠ sumPerm W d p := fun e =>
        htp (sumPerm_injective hWinj hmap hd.1 e)
      have hdisj := disjoint_sup_sup_of_ne hind (Ne.symm htp) (Ne.symm h1) (Ne.symm htq)
        (Ne.symm h2)
      exact hu (Submodule.disjoint_def.mp hdisj u hupq hut)
    rw [hwW] at hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hfixed t ht]

theorem IsTranspOn.bilin_rel (B : LinearMap.BilinForm F V) {d : V ≃ₗ[F] V}
    (hdSp : d ∈ spGroup B) {p q : Fin 4} (hd : IsTranspOn W d p q) (hwW : ∀ i, W i = F ∙ w i)
    {c : F} (hc : c • w q = d (w p)) (t : Fin 4) (htp : t ≠ p) (htq : t ≠ q) :
    B (w p) (w t) = c * B (w q) (w t) := by
  have hwt : d (w t) = w t :=
    hd.fix t htp htq _ (by rw [hwW]; exact Submodule.mem_span_singleton_self _)
  have h : B (d (w p)) (d (w t)) = B (w p) (w t) := hdSp (w p) (w t)
  rw [← hc, hwt, LinearMap.map_smul₂, smul_eq_mul] at h
  exact h.symm

theorem IsTranspOn.bilin_ne_zero [CharP F 2] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hind : iSupIndep W)
    (htop : (⨆ i, W i) = ⊤) (hwW : ∀ i, W i = F ∙ w i) (hw0 : ∀ i, w i ≠ 0) {d : V ≃ₗ[F] V}
    (hdSp : d ∈ spGroup B) {p q : Fin 4} (hd : IsTranspOn W d p q) : B (w p) (w q) ≠ 0 := by
  intro h0
  have hwmem : ∀ t, w t ∈ W t := fun t => by
    rw [hwW]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ : ∃ c : F, c • w q = d (w p) := by
    have h1 := hd.map_left _ (hwmem p)
    rw [hwW] at h1
    exact Submodule.mem_span_singleton.mp h1
  have hx : w p - c • w q = 0 := by
    apply eq_zero_of_bilin_lines B hnd htop hwW
    intro t
    rw [LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul]
    by_cases htp : t = p
    · rw [htp, halt, bilin_symm B halt, h0, mul_zero, sub_zero]
    by_cases htq : t = q
    · rw [htq, halt, h0, mul_zero, sub_zero]
    rw [hd.bilin_rel B hdSp hwW hc t htp htq, sub_self]
  have hwpq : w p ∈ W q := by
    rw [sub_eq_zero.mp hx, hwW]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  exact hw0 p (Submodule.disjoint_def.mp (hind.pairwiseDisjoint hd.ne) _ (hwmem p) hwpq)

theorem eq_one_of_lines_fixed [CharP F 2] (B : LinearMap.BilinForm F V) (htop : (⨆ i, W i) = ⊤)
    (hwW : ∀ i, W i = F ∙ w i) {g : V ≃ₗ[F] V} (hgSp : g ∈ spGroup B)
    (hfix : ∀ t, g (w t) ∈ W t) {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (mij : B (w i) (w j) ≠ 0)
    (mik : B (w i) (w k) ≠ 0) (mjk : B (w j) (w k) ≠ 0) (mil : B (w i) (w l) ≠ 0) : g = 1 := by
  have hκ : ∀ t, ∃ κ : F, κ • w t = g (w t) := fun t => by
    have h1 := hfix t
    rw [hwW] at h1
    exact Submodule.mem_span_singleton.mp h1
  choose κ hκ using hκ
  have hprod : ∀ s t, B (w s) (w t) ≠ 0 → κ s * κ t = 1 := by
    intro s t hst
    have h : B (g (w s)) (g (w t)) = B (w s) (w t) := hgSp (w s) (w t)
    rw [← hκ s, ← hκ t, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc] at h
    exact mul_right_cancel₀ hst (h.trans (one_mul _).symm)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hone : ∀ x : F, x * x = 1 → x = 1 := fun x hx => by
    have hsq : (x - 1) * (x - 1) = 0 := by linear_combination hx + (1 - x) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
  have eij := hprod i j mij
  have eik := hprod i k mik
  have ejk := hprod j k mjk
  have eil := hprod i l mil
  have hjk' : κ j = κ k := by linear_combination (κ k) * eij - (κ j) * eik
  have hj1 : κ j = 1 := hone _ (by rw [← hjk'] at ejk; exact ejk)
  have hi1 : κ i = 1 := by rw [hj1, mul_one] at eij; exact eij
  have hk1 : κ k = 1 := hjk'.symm.trans hj1
  have hl1 : κ l = 1 := by rw [hi1, one_mul] at eil; exact eil
  have key : ∀ t, κ t = 1 → g (w t) = (1 : V ≃ₗ[F] V) (w t) := fun t ht => by
    simp [← hκ t, ht]
  apply eq_of_lines htop hwW
  intro t
  rcases eq_of_four hij hik hil hjk hjl hkl t with rfl | rfl | rfl | rfl
  exacts [key _ hi1, key _ hj1, key _ hk1, key _ hl1]

end Lines

theorem false_of_disjoint_transp_perm [Finite V] {G₀ : Subgroup (V ≃ₗ[F] V)}
    (hirr : IsIrredOnV G₀) (heven : Even (Nat.card V)) (σ : (V ≃ₗ[F] V) → Fin 4 → Fin 4)
    (hmul : ∀ g ∈ G₀, ∀ h ∈ G₀, ∀ t, σ (g * h) t = σ g (σ h t)) (hone : ∀ t, σ 1 t = t)
    (hK : ∀ g ∈ G₀, (∀ t, σ g t = t) → g = 1) {d₁ d₂ : V ≃ₗ[F] V} (hd₁ : d₁ ∈ G₀)
    (hd₂ : d₂ ∈ G₀) {p q r s : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) (h1p : σ d₁ p = q) (h1q : σ d₁ q = p)
    (h1 : ∀ t, t ≠ p → t ≠ q → σ d₁ t = t) (h2r : σ d₂ r = s) (h2s : σ d₂ s = r)
    (h2 : ∀ t, t ≠ r → t ≠ s → σ d₂ t = t) : False := by
  have hinv : ∀ g ∈ G₀, ∀ t, σ g (σ g⁻¹ t) = t := fun g hg t => by
    rw [← hmul g hg _ (G₀.inv_mem hg), mul_inv_cancel, hone]
  have hinv' : ∀ g ∈ G₀, ∀ t, σ g⁻¹ (σ g t) = t := fun g hg t => by
    rw [← hmul _ (G₀.inv_mem hg) g hg, inv_mul_cancel, hone]
  let N : Subgroup (V ≃ₗ[F] V) :=
    { carrier := {g | g ∈ G₀ ∧ ∀ ε : Fin 4 → Fin 4, IsFpfInv ε → ∀ t, σ g (ε t) = ε (σ g t)}
      mul_mem' := by
        rintro g h ⟨hg, hgε⟩ ⟨hh, hhε⟩
        refine ⟨G₀.mul_mem hg hh, fun ε hε t => ?_⟩
        rw [hmul g hg h hh, hmul g hg h hh, hhε ε hε, hgε ε hε]
      one_mem' := ⟨G₀.one_mem, fun ε _ t => by rw [hone, hone]⟩
      inv_mem' := by
        rintro g ⟨hg, hgε⟩
        refine ⟨G₀.inv_mem hg, fun ε hε t => ?_⟩
        have h := hgε ε hε (σ g⁻¹ t)
        rw [hinv g hg] at h
        calc σ g⁻¹ (ε t) = σ g⁻¹ (σ g (ε (σ g⁻¹ t))) := by rw [h]
          _ = ε (σ g⁻¹ t) := hinv' g hg _ }
  have hN2 : IsPGroup 2 N := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨hx, hxε⟩ := x.2
    have hsq : (x : V ≃ₗ[F] V) * x = 1 :=
      hK _ (G₀.mul_mem hx hx) fun t => by rw [hmul _ hx _ hx, sq_eq_of_comm_isFpfInv hxε]
    rw [pow_one, pow_two]
    exact Subtype.ext hsq
  have hNG : ∀ g ∈ G₀, ∀ h ∈ N, g * h * g⁻¹ ∈ N := by
    rintro g hg h ⟨hh, hhε⟩
    refine ⟨G₀.mul_mem (G₀.mul_mem hg hh) (G₀.inv_mem hg), fun ε hε t => ?_⟩
    have hc : IsFpfInv fun t => σ g⁻¹ (ε (σ g t)) := hε.conj (hinv' g hg) (hinv g hg)
    have key := hhε _ hc (σ g⁻¹ t)
    simp only [hinv g hg] at key
    rw [hmul _ (G₀.mul_mem hg hh) _ (G₀.inv_mem hg), hmul g hg h hh,
      hmul _ (G₀.mul_mem hg hh) _ (G₀.inv_mem hg), hmul g hg h hh, key, hinv g hg]
  have hdN : d₁ * d₂ ∈ N := by
    refine ⟨G₀.mul_mem hd₁ hd₂, fun ε hε t => ?_⟩
    have hfpf := isFpfInv_comp_of_transp hpq hpr hps hqr hqs hrs h1p h1q h1 h2r h2s h2
    rw [hmul _ hd₁ _ hd₂, hmul _ hd₁ _ hd₂]
    exact hfpf.comm hε t
  have hbot := core_trivial G₀ hirr heven N hN2 hNG
  have hd1 : d₁ * d₂ = 1 := by
    have hmem : d₁ * d₂ ∈ (⊥ : Subgroup (V ≃ₗ[F] V)) := hbot ▸ hdN
    exact Subgroup.mem_bot.mp hmem
  have hp := hmul _ hd₁ _ hd₂ p
  rw [hd1, hone, h2 p hpr hps, h1p] at hp
  exact hpq hp

section Four

variable {W : Fin 4 → Submodule F V} {w : Fin 4 → V} {G₀ : Subgroup (V ≃ₗ[F] V)}

theorem false_of_overlap [Finite F] [CharP F 2] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀)
    (hne : ∀ i, W i ≠ ⊥) (hind : iSupIndep W) (htop : (⨆ i, W i) = ⊤)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j) (hwW : ∀ i, W i = F ∙ w i)
    (hw0 : ∀ i, w i ≠ 0) {a b : V ≃ₗ[F] V} (ha : a ∈ transvSet G₀) (hb : b ∈ transvSet G₀)
    {i j k : Fin 4} (hai : IsTranspOn W a i j) (hbi : IsTranspOn W b i k) (hjk : j ≠ k) :
    False := by
  obtain ⟨hfin, heven⟩ := finite_even_card (V := V) hdim
  have hWinj := summand_injective hne hind
  have hij := hai.ne
  have hik := hbi.ne
  obtain ⟨l, hli, hlj, hlk⟩ := exists_ne_three i j k
  have hwmem : ∀ t, w t ∈ W t := fun t => by
    rw [hwW]
    exact Submodule.mem_span_singleton_self _
  have mij := hai.bilin_ne_zero B halt hnd hind htop hwW hw0 (hSp ha.1)
  have mik := hbi.bilin_ne_zero B halt hnd hind htop hwW hw0 (hSp hb.1)
  obtain ⟨lam, hlam⟩ : ∃ lam : F, lam • w j = a (w i) := by
    have h1 := hai.map_left _ (hwmem i)
    rw [hwW] at h1
    exact Submodule.mem_span_singleton.mp h1
  obtain ⟨mu, hmu⟩ : ∃ mu : F, mu • w k = b (w i) := by
    have h1 := hbi.map_left _ (hwmem i)
    rw [hwW] at h1
    exact Submodule.mem_span_singleton.mp h1
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hlam
    exact hw0 i ((LinearEquiv.map_eq_zero_iff a).mp hlam.symm)
  have hmu0 : mu ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hmu
    exact hw0 i ((LinearEquiv.map_eq_zero_iff b).mp hmu.symm)
  have mjk : B (w j) (w k) ≠ 0 := fun h =>
    mik (by rw [hai.bilin_rel B (hSp ha.1) hwW hlam k hik.symm hjk.symm, h, mul_zero])
  have mil : B (w i) (w l) ≠ 0 := by
    intro h0
    have hjl : B (w j) (w l) = 0 := by
      have h1 := hai.bilin_rel B (hSp ha.1) hwW hlam l hli hlj
      rw [h0] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left hlam0
    have hkl : B (w k) (w l) = 0 := by
      have h1 := hbi.bilin_rel B (hSp hb.1) hwW hmu l hli hlk
      rw [h0] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left hmu0
    apply hw0 l
    apply eq_zero_of_bilin_lines B hnd htop hwW
    intro t
    rcases eq_of_four hij hik (Ne.symm hli) hjk (Ne.symm hlj) (Ne.symm hlk) t with
      rfl | rfl | rfl | rfl
    · rw [bilin_symm B halt]
      exact h0
    · rw [bilin_symm B halt]
      exact hjl
    · rw [bilin_symm B halt]
      exact hkl
    · exact halt _
  have hK : ∀ g ∈ G₀, (∀ t, sumPerm W g t = t) → g = 1 := fun g hg hfix =>
    eq_one_of_lines_fixed B htop hwW (hSp hg)
      (fun t => by
        have h1 := apply_mem_sumPerm hmap hg (hwmem t)
        rwa [hfix] at h1)
      hij hik (Ne.symm hli) hjk (Ne.symm hlj) (Ne.symm hlk) mij mik mjk mil
  have klein : ∀ d₁ ∈ G₀, ∀ d₂ ∈ G₀, ∀ p q r s : Fin 4, p ≠ r → p ≠ s → q ≠ r → q ≠ s →
      IsTranspOn W d₁ p q → IsTranspOn W d₂ r s → False := by
    intro d₁ hd₁ d₂ hd₂ p q r s hpr hps hqr hqs h₁ h₂
    exact false_of_disjoint_transp_perm hirr heven (sumPerm W)
      (fun g hg h hh t => sumPerm_mul hWinj hmap hg hh t) (sumPerm_one hWinj hmap) hK hd₁ hd₂
      h₁.ne hpr hps hqr hqs h₂.ne
      (h₁.sumPerm_left hne hind hmap hd₁) (h₁.sumPerm_right hne hind hmap hd₁)
      (fun t htp htq => h₁.sumPerm_fix hne hind hmap hd₁ htp htq)
      (h₂.sumPerm_left hne hind hmap hd₂) (h₂.sumPerm_right hne hind hmap hd₂)
      (fun t htr hts => h₂.sumPerm_fix hne hind hmap hd₂ htr hts)
  have hc : IsTranspOn W (a * b * a⁻¹) j k := by
    have h1 := hbi.conj hWinj hmap ha.1
    rwa [hai.sumPerm_left hne hind hmap ha.1,
      hai.sumPerm_fix hne hind hmap ha.1 hik.symm hjk.symm] at h1
  have hcG : a * b * a⁻¹ ∈ G₀ := G₀.mul_mem (G₀.mul_mem ha.1 hb.1) (G₀.inv_mem ha.1)
  obtain ⟨h, hh, hhi⟩ := exists_sumPerm_eq hirr hne hind htop hmap i l
  have he : IsTranspOn W (h * a * h⁻¹) l (sumPerm W h j) := by
    have h1 := hai.conj hWinj hmap hh
    rwa [hhi] at h1
  have heG : h * a * h⁻¹ ∈ G₀ := G₀.mul_mem (G₀.mul_mem hh ha.1) (G₀.inv_mem hh)
  rcases eq_of_four hij hik (Ne.symm hli) hjk (Ne.symm hlj) (Ne.symm hlk) (sumPerm W h j) with
    hx | hx | hx | hx
  · rw [hx] at he
    exact klein _ heG _ hcG l i j k hlj hlk hij hik he hc
  · rw [hx] at he
    exact klein _ heG _ hb.1 l j i k hli hlk (Ne.symm hij) hjk he hbi
  · rw [hx] at he
    exact klein _ heG _ ha.1 l k i j hli hlj (Ne.symm hik) (Ne.symm hjk) he hai
  · exact he.ne hx.symm

theorem not_connected_of_four_summands [Finite F] [CharP F 2] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4) (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B)
    (hirr : IsIrredOnV G₀) (hD : (transvSet G₀).Nonempty) {W : Fin 4 → Submodule F V}
    (hne : ∀ i, W i ≠ ⊥) (hind : iSupIndep W) (htop : (⨆ i, W i) = ⊤)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j)
    (hW1 : ∀ i, Module.finrank F (W i) = 1) : ¬ (advGraph G₀).Connected := by
  have hw : ∀ i, ∃ v : V, v ≠ 0 ∧ W i = F ∙ v := fun i => by
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp (hW1 i)
    refine ⟨v, fun h => hv0 (Subtype.ext h), le_antisymm (fun x hx => ?_) ?_⟩
    · obtain ⟨c, hc⟩ := hv ⟨x, hx⟩
      exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr v.2
  choose w hw0 hwW using hw
  have hWinj := summand_injective hne hind
  obtain ⟨a, haD⟩ := hD
  obtain ⟨p, q, hapq⟩ := exists_transpOn B halt hnd hSp hne hind htop hmap hwW haD
  by_cases hov : ∃ b ∈ transvSet G₀, ∃ i j k : Fin 4, j ≠ k ∧ IsTranspOn W a i j ∧
      IsTranspOn W b i k
  · obtain ⟨b, hb, i, j, k, hjk, hai, hbi⟩ := hov
    exact (false_of_overlap B halt hnd hdim hSp hirr hne hind htop hmap hwW hw0 haD hb hai hbi
      hjk).elim
  push Not at hov
  obtain ⟨r, s, hrs, hrp, hrq, hsp, hsq⟩ := exists_compl_pair hapq.ne
  have hexh : ∀ t, t = p ∨ t = q ∨ t = r ∨ t = s :=
    eq_of_four hapq.ne (Ne.symm hrp) (Ne.symm hsp) (Ne.symm hrq) (Ne.symm hsq) hrs
  have hcls : ∀ b ∈ transvSet G₀, ∀ p' q', IsTranspOn W b p' q' →
      (p' = p ∧ q' = q) ∨ (p' = q ∧ q' = p) ∨ (p' ≠ p ∧ p' ≠ q ∧ q' ≠ p ∧ q' ≠ q) := by
    intro b hb p' q' hb'
    by_cases h1 : p' = p
    · rw [h1] at hb'
      by_cases h2 : q' = q
      · exact Or.inl ⟨h1, h2⟩
      · exact absurd hb' (hov b hb p q q' (Ne.symm h2) hapq)
    by_cases h2 : p' = q
    · rw [h2] at hb'
      by_cases h3 : q' = p
      · exact Or.inr (Or.inl ⟨h2, h3⟩)
      · exact absurd hb' (hov b hb q p q' (Ne.symm h3) hapq.symm)
    by_cases h3 : q' = p
    · rw [h3] at hb'
      exact absurd hb'.symm (hov b hb p q p' (Ne.symm h2) hapq)
    by_cases h4 : q' = q
    · rw [h4] at hb'
      exact absurd hb'.symm (hov b hb q p p' (Ne.symm h1) hapq.symm)
    exact Or.inr (Or.inr ⟨h1, h2, h3, h4⟩)
  have hshape : ∀ b ∈ transvSet G₀, IsTranspOn W b p q ∨ IsTranspOn W b r s := by
    intro b hb
    obtain ⟨p', q', hb'⟩ := exists_transpOn B halt hnd hSp hne hind htop hmap hwW hb
    rcases hcls b hb p' q' hb' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · rw [h1, h2] at hb'
      exact Or.inl hb'
    · rw [h1, h2] at hb'
      exact Or.inl hb'.symm
    · right
      rcases hexh p' with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · rcases hexh q' with h' | h' | h' | h'
        · exact absurd h' h3
        · exact absurd h' h4
        · exact absurd (h.trans h'.symm) hb'.ne
        · rw [h, h'] at hb'
          exact hb'
      · rcases hexh q' with h' | h' | h' | h'
        · exact absurd h' h3
        · exact absurd h' h4
        · rw [h, h'] at hb'
          exact hb'.symm
        · exact absurd (h.trans h'.symm) hb'.ne
  have hblk : ∀ b ∈ transvSet G₀,
      ((∀ x ∈ W p ⊔ W q, b x ∈ W p ⊔ W q) ∧ ∀ x ∈ W r ⊔ W s, b x ∈ W r ⊔ W s) ∧
        ((∀ x ∈ W p ⊔ W q, b x = x) ∨ ∀ x ∈ W r ⊔ W s, b x = x) := by
    intro b hb
    rcases hshape b hb with h | h
    · obtain ⟨h1, h2⟩ := h.blocks hrp hrq hsp hsq
      exact ⟨⟨h1, fun x hx => by rw [h2 x hx]; exact hx⟩, Or.inr h2⟩
    · obtain ⟨h1, h2⟩ := h.blocks (Ne.symm hrp) (Ne.symm hsp) (Ne.symm hrq) (Ne.symm hsq)
      exact ⟨⟨fun x hx => by rw [h2 x hx]; exact hx, h1⟩, Or.inl h2⟩
  have hdisj : Disjoint (W p ⊔ W q) (W r ⊔ W s) :=
    disjoint_sup_sup_of_ne hind (Ne.symm hrp) (Ne.symm hsp) (Ne.symm hrq) (Ne.symm hsq)
  have htop' : W p ⊔ W q ⊔ (W r ⊔ W s) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun t => ?_
    rcases hexh t with rfl | rfl | rfl | rfl
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_left.trans le_sup_right
    · exact le_sup_right.trans le_sup_right
  obtain ⟨g, hg, x, hx, hgx⟩ : ∃ g ∈ G₀, ∃ x ∈ W p ⊔ W q, g x ∉ W p ⊔ W q := by
    by_contra hcon
    push Not at hcon
    rcases hirr _ hcon with h | h
    · exact hne p (eq_bot_iff.mpr (h ▸ le_sup_left))
    · rw [h, top_disjoint] at hdisj
      exact hne r (eq_bot_iff.mpr (hdisj ▸ le_sup_left))
  have he := hapq.conj hWinj hmap hg
  have heD : g * a * g⁻¹ ∈ transvSet G₀ := conj_mem_transvSet hg haD
  rcases hcls _ heD _ _ he with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · exact absurd (mapsTo_sup_of_sumPerm hmap hg (Or.inl h1) (Or.inr h2) x hx) hgx
  · exact absurd (mapsTo_sup_of_sumPerm hmap hg (Or.inr h1) (Or.inl h2) x hx) hgx
  have hinj := sumPerm_injective hWinj hmap hg
  have hgp : sumPerm W g p = r ∨ sumPerm W g p = s := by
    rcases hexh (sumPerm W g p) with h | h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact Or.inl h
    · exact Or.inr h
  have hgq : sumPerm W g q = r ∨ sumPerm W g q = s := by
    rcases hexh (sumPerm W g q) with h | h | h | h
    · exact absurd h h3
    · exact absurd h h4
    · exact Or.inl h
    · exact Or.inr h
  have hback : ∀ t, t ≠ p → t ≠ q → sumPerm W g t = p ∨ sumPerm W g t = q := by
    intro t htp htq
    rcases hexh (sumPerm W g t) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (false_of_three_in_pair hgp hgq (Or.inl h) (fun e => hapq.ne (hinj e))
        (fun e => htp (hinj e).symm) (fun e => htq (hinj e).symm)).elim
    · exact (false_of_three_in_pair hgp hgq (Or.inr h) (fun e => hapq.ne (hinj e))
        (fun e => htp (hinj e).symm) (fun e => htq (hinj e).symm)).elim
  exact not_connected_of_two_blocks hdisj htop' ⟨a, haD⟩ (fun b hb => (hblk b hb).1)
    (fun b hb => (hblk b hb).2) hg (mapsTo_sup_of_sumPerm hmap hg hgp hgq)
    (mapsTo_sup_of_sumPerm hmap hg (hback r hrp hrq) (hback s hsp hsq))

end Four

end G46Imprim

end CFSG.Quasithin.SimsG4
