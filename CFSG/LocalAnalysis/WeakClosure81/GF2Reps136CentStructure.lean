module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136CentCoord

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

theorem cent_structure {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} (hk3 : k = 3) {I : Fin k → Subgroup Q}
    (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ I i → J = ⊥ ∨ J = I i)
    (hspan : ⨆ i, I i = ⊤) (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {X : Subgroup (MulAut Q)} (hXc : X ≤ Subgroup.centralizer (Λ : Set (MulAut Q)))
    (hXp : ⁅X, X⁆ = X) (hiso : ∀ i j, SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    (hcardX : Nat.card X = 168) :
    (∃ x ∈ X, orderOf x = 7 ∧ ∀ q : Q, x q = q → q = 1) ∧
    (∀ N : Subgroup Q, StableUnder Λ N → StableUnder X N → N = ⊥ ∨ N = ⊤) ∧
    Subgroup.centralizer ((Λ ⊔ X : Subgroup (MulAut Q)) : Set (MulAut Q)) = ⊥ ∧
    ∀ N : Subgroup Q, StableUnder Λ N → N ≠ ⊥ → ∃ x ∈ X, ∃ n ∈ N, x n ≠ n := by
  subst hk3
  classical
  have hstab' : ∀ i, ∀ g ∈ Λ, ∀ y ∈ I i, g y ∈ I i := fun i => hstab i
  have hsimple' : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q,
      (∀ g ∈ Λ, ∀ y ∈ J, g y ∈ J) → J ≤ I i → J = ⊥ ∨ J = I i :=
    fun i => ⟨(hsimple i).1, fun J hJ => (hsimple i).2 J hJ⟩
  let P : w1369_s16h_Proj I Λ := w1369_s16h_mkProj hstab' hspan hind
  have hend' : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ y, f (g y) = g (f y)) →
      (∀ y ∈ I i, f y ∈ I i) → (∀ j, j ≠ i → ∀ y ∈ I j, f y = 1) →
      (∀ y ∈ I i, f y = y) ∨ (∀ y ∈ I i, f y = 1) := by
    intro i f hf hm hk
    have hne : (if i = 0 then 1 else 0) ≠ i := by
      split_ifs with h
      · rw [h]; decide
      · exact fun hh => h hh.symm
    exact hend i (if i = 0 then 1 else 0) hne.symm (hiso i _) f hf hm hk
  let M : Subgroup.centralizer (Λ : Set (MulAut Q)) →* GL (Fin 3) (ZMod 2) :=
    w1369_s16h_matrixHom hQ P hstab' hsimple' hend'
  have hMinj : Function.Injective M :=
    w1369_s16h_matrixHom_injective hQ P hstab' hsimple' hend'
  let MX : X →* GL (Fin 3) (ZMod 2) := M.comp (Subgroup.inclusion hXc)
  have hMXinj : Function.Injective MX := hMinj.comp (Subgroup.inclusion_injective hXc)
  have hcardGL : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
    rw [Matrix.card_GL_field (𝔽 := ZMod 2) 3, Fin.prod_univ_three, ZMod.card]
    norm_num
  have hcardRange : Nat.card MX.range = 168 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hMXinj).toEquiv, hcardX]
  have hMXtop : MX.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq MX.range ?_
    rw [hcardRange, hcardGL]
  obtain ⟨xX, hxX⟩ : ∃ y : X, MX y = w1369_rho := by
    have : w1369_rho ∈ MX.range := hMXtop ▸ Subgroup.mem_top w1369_rho
    exact MonoidHom.mem_range.mp this
  let x0 : MulAut Q := (xX : MulAut Q)
  have hx0mem : x0 ∈ X := xX.2
  have hx0cent : x0 ∈ Subgroup.centralizer (Λ : Set (MulAut Q)) := hXc xX.2
  have hx0ord : orderOf x0 = 7 := by
    have h1 : orderOf (MX xX) = orderOf xX := orderOf_injective MX hMXinj xX
    rw [hxX, w1369_rho_order] at h1
    rw [show orderOf x0 = orderOf xX from Subgroup.orderOf_coe xX, ← h1]
  have hx0mat : w1369_s16h_matrix P x0 = w1369_rho.val :=
    congrArg Units.val hxX
  have hx0mat_pow : ∀ n : ℕ, w1369_s16h_matrix P (x0 ^ n) = w1369_rho.val ^ n := by
    intro n
    have h1 := congrArg Units.val (map_pow M ⟨x0, hx0cent⟩ n)
    simpa [M, w1369_s16h_matrixHom, Subgroup.coe_pow, hx0mat] using h1
  let β : ∀ i : Fin 3, ↥(I 0) ≃* ↥(I i) := fun i => w1369_secEquivOfIso (hiso 0 i)
  have hβ : ∀ i, ∀ g (hg : g ∈ Λ) (y : ↥(I 0)),
      ((β i ⟨g (y : Q), hstab' 0 g hg (y : Q) y.2⟩ : ↥(I i)) : Q) =
        g ((β i y : ↥(I i)) : Q) :=
    fun i => w1369_secEquivOfIso_equivariant (hiso 0 i)
  have htrans : ∀ S : Subgroup Q,
      (S ≠ ⊥ ∧ StableUnder Λ S ∧
        ∀ T : Subgroup Q, StableUnder Λ T → T ≤ S → T = ⊥ ∨ T = S) →
      ∀ S' : Subgroup Q,
      (S' ≠ ⊥ ∧ StableUnder Λ S' ∧
        ∀ T : Subgroup Q, StableUnder Λ T → T ≤ S' → T = ⊥ ∨ T = S') →
      ∃ n : Fin 7, S' = S.map ((x0 ^ (n : ℕ)).toMonoidHom) := by
    intro S hS S' hS'
    obtain ⟨φ, hφe, hφinj, hφrange⟩ :=
      w1369_exists_iso P β hstab' hsimple' hβ hS.2.1 hS.1 hS.2.2
    obtain ⟨ψ, hψe, hψinj, hψrange⟩ :=
      w1369_exists_iso P β hstab' hsimple' hβ hS'.2.1 hS'.1 hS'.2.2
    have hc : w1369_coord P φ ≠ 0 :=
      w1369_coord_ne_zero P β hstab' hsimple' hend' hβ hφe hφinj
    have hd : w1369_coord P ψ ≠ 0 :=
      w1369_coord_ne_zero P β hstab' hsimple' hend' hβ hψe hψinj
    obtain ⟨n, hn⟩ := w1369_rho_orbit (w1369_coord P φ) (w1369_coord P ψ) hc hd
    refine ⟨n, ?_⟩
    have hxkn : x0 ^ (n : ℕ) ∈ Subgroup.centralizer (Λ : Set (MulAut Q)) :=
      Subgroup.pow_mem _ hx0cent n
    have hcomp_e : ∀ g (hg : g ∈ Λ) (y : ↥(I 0)),
        ((x0 ^ (n : ℕ)).toMonoidHom.comp φ) ⟨g (y : Q), hstab' 0 g hg (y : Q) y.2⟩ =
          g (((x0 ^ (n : ℕ)).toMonoidHom.comp φ) y) := by
      intro g hg y
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hφe g hg y]
      exact w1369_s16h_cent_comm hxkn g hg (φ y)
    have hcoord : w1369_coord P ((x0 ^ (n : ℕ)).toMonoidHom.comp φ) =
        (↑(w1369_rho ^ (n : ℕ)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
          w1369_coord P φ := by
      rw [w1369_coord_comp hQ P β hstab' hsimple' hend' hβ hxkn hφe, hx0mat_pow,
        Units.val_pow_eq_pow_val]
    have hφψ : (x0 ^ (n : ℕ)).toMonoidHom.comp φ = ψ := by
      rw [w1369_Phi_coord P β hstab' hsimple' hend' hβ hcomp_e, hcoord, hn]
      exact (w1369_Phi_coord P β hstab' hsimple' hend' hβ hψe).symm
    calc S' = ψ.range := hψrange.symm
      _ = ((x0 ^ (n : ℕ)).toMonoidHom.comp φ).range := by rw [hφψ]
      _ = φ.range.map ((x0 ^ (n : ℕ)).toMonoidHom) := MonoidHom.range_comp _ _
      _ = S.map ((x0 ^ (n : ℕ)).toMonoidHom) := by rw [hφrange]
  have hpart1 : ∃ y ∈ X, orderOf y = 7 ∧ ∀ q : Q, y q = q → q = 1 := by
    refine ⟨x0, hx0mem, hx0ord, ?_⟩
    intro q hq
    by_contra hqne
    have hNstab : StableUnder Λ (fixV (Subgroup.zpowers x0)) := by
      intro g hg y hy
      rw [mem_fixV] at hy ⊢
      intro x' hx'
      have hx'cent : x' ∈ Subgroup.centralizer (Λ : Set (MulAut Q)) :=
        (Subgroup.zpowers_le.mpr hx0cent) hx'
      rw [w1369_s16h_cent_comm hx'cent g hg y]
      exact congrArg g (hy x' hx')
    have hNne : fixV (Subgroup.zpowers x0) ≠ ⊥ := by
      intro hbot
      have hqmem : q ∈ fixV (Subgroup.zpowers x0) := by
        rw [mem_fixV]
        intro x' hx'
        have h1 : x' ∈ MulAction.stabilizer (MulAut Q) q :=
          (Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hq)) hx'
        rwa [MulAction.mem_stabilizer_iff] at h1
      rw [hbot] at hqmem
      exact hqne (Subgroup.mem_bot.mp hqmem)
    obtain ⟨S, hSN, hSstab, hSne, hSsimple⟩ := w1369_exists_simple_sub hNstab hNne
    obtain ⟨φ, hφe, hφinj, hφrange⟩ :=
      w1369_exists_iso P β hstab' hsimple' hβ hSstab hSne hSsimple
    have hfixS : ∀ y ∈ S, x0 y = y := by
      intro y hy
      have h1 := hSN hy
      rw [mem_fixV] at h1
      exact h1 x0 (Subgroup.mem_zpowers x0)
    have hxφ : x0.toMonoidHom.comp φ = φ := by
      ext y
      exact hfixS (φ y) (by rw [← hφrange]; exact MonoidHom.mem_range.mpr ⟨y, rfl⟩)
    have hcoord : w1369_coord P φ = w1369_rho.val *ᵥ w1369_coord P φ := by
      have h1 := w1369_coord_comp hQ P β hstab' hsimple' hend' hβ hx0cent hφe
      rw [hxφ, hx0mat] at h1
      exact h1
    have hc : w1369_coord P φ ≠ 0 :=
      w1369_coord_ne_zero P β hstab' hsimple' hend' hβ hφe hφinj
    exact hc (w1369_rho_fixed (w1369_coord P φ) hcoord.symm)
  have hpart2 : ∀ N : Subgroup Q, StableUnder Λ N → StableUnder X N → N = ⊥ ∨ N = ⊤ := by
    intro N hNstab hNXstab
    by_cases hN : N = ⊥
    · exact Or.inl hN
    · right
      obtain ⟨S, hSN, hSstab, hSne, hSsimple⟩ := w1369_exists_simple_sub hNstab hN
      have hmapN : ∀ g ∈ X, N.map g.toMonoidHom = N := by
        intro g hg
        apply le_antisymm
        · intro y hy
          obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
          exact hNXstab g hg n hn
        · intro y hy
          have h1 : g⁻¹ y ∈ N := hNXstab g⁻¹ (X.inv_mem hg) y hy
          exact Subgroup.mem_map.mpr ⟨g⁻¹ y, h1, by simp⟩
      have hIle : ∀ i : Fin 3, I i ≤ N := by
        intro i
        obtain ⟨n, hn⟩ := htrans S ⟨hSne, hSstab, hSsimple⟩ (I i)
          ⟨(hsimple' i).1, hstab' i, (hsimple' i).2⟩
        rw [hn]
        calc S.map ((x0 ^ (n : ℕ)).toMonoidHom) ≤ N.map ((x0 ^ (n : ℕ)).toMonoidHom) :=
              Subgroup.map_mono hSN
          _ = N := hmapN _ (Subgroup.pow_mem X hx0mem n)
      rw [eq_top_iff, ← hspan]
      exact iSup_le hIle
  have hpart3 : Subgroup.centralizer ((Λ ⊔ X : Subgroup (MulAut Q)) : Set (MulAut Q)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    have hcΛ : c ∈ Subgroup.centralizer (Λ : Set (MulAut Q)) :=
      Subgroup.centralizer_le (le_sup_left : Λ ≤ Λ ⊔ X) (by simpa using hc)
    have hcX : c ∈ Subgroup.centralizer (X : Set (MulAut Q)) :=
      Subgroup.centralizer_le (le_sup_right : X ≤ Λ ⊔ X) (by simpa using hc)
    have hMc : M ⟨c, hcΛ⟩ ∈ Subgroup.center (GL (Fin 3) (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, hy⟩ : ∃ y : X, MX y = g := by
        have : g ∈ MX.range := hMXtop ▸ Subgroup.mem_top g
        exact MonoidHom.mem_range.mp this
      have hcomm : c * (y : MulAut Q) = (y : MulAut Q) * c :=
        (Subgroup.mem_centralizer_iff.mp hcX (y : MulAut Q) y.2).symm
      have h1 : M ⟨c, hcΛ⟩ * g = g * M ⟨c, hcΛ⟩ := by
        have h2 : M (⟨c, hcΛ⟩ * (Subgroup.inclusion hXc y)) =
            M ((Subgroup.inclusion hXc y) * ⟨c, hcΛ⟩) := by
          congr 1
          exact Subtype.ext hcomm
        rw [map_mul, map_mul] at h2
        rw [show M ((Subgroup.inclusion hXc) y) = g from hy] at h2
        exact h2
      exact h1.symm
    rw [w1369_center_GL32, Subgroup.mem_bot] at hMc
    have hc1 : (⟨c, hcΛ⟩ : Subgroup.centralizer (Λ : Set (MulAut Q))) = 1 := hMinj (by
      rw [map_one]; exact hMc)
    exact Subtype.ext_iff.mp hc1
  have hpart4 : ∀ N : Subgroup Q, StableUnder Λ N → N ≠ ⊥ →
      ∃ y ∈ X, ∃ n ∈ N, y n ≠ n := by
    intro N hNstab hNne
    by_contra hcon
    push Not at hcon
    have hNXstab : StableUnder X N := fun y hy n hn => by rw [hcon y hy n hn]; exact hn
    rcases hpart2 N hNstab hNXstab with h | h
    · exact hNne h
    · have hXbot : X = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro y hy
        ext q
        exact hcon y hy q (by rw [h]; exact Subgroup.mem_top q)
      rw [hXbot, Subgroup.card_bot] at hcardX
      norm_num at hcardX
  exact ⟨hpart1, hpart2, hpart3, hpart4⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
