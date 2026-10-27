module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517A5Setup

public section

namespace CFSG.Quasithin.H13.A5Push

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin Equiv

variable {G : Type} [Group G]

theorem sub_eq_add_vec (f g : Fin 5 → ZMod 2) : f - g = f + g := by
  funext i
  exact CharTwo.sub_eq_add (f i) (g i)

theorem _root_.CFSG.Quasithin.H13.S5Frame.c_comm {Y W : Subgroup G} (F : S5Frame Y W) (s : ↥Y)
    (u : ↥W)
    (hsu : (s : G) * u * (s : G)⁻¹ * (u : G)⁻¹ ∈ W) :
    F.c ⟨_, hsu⟩ = pmv (F.ρ s) (F.c u) + F.c u := by
  have h1 : (s : G) * u * (s : G)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (F.le s.2) u).mp u.2
  have e : (⟨_, hsu⟩ : ↥W) = ⟨_, h1⟩ * u⁻¹ := rfl
  rw [e, F.c_mul, F.equiv s u h1, F.c_inv]

theorem _root_.CFSG.Quasithin.H13.S5Frame.c_conj_eq {Y W : Subgroup G} (F : S5Frame Y W)
    (s : ↥Y) (u v : ↥W)
    (h : (s : G) * u * (s : G)⁻¹ = v) : F.c v = pmv (F.ρ s) (F.c u) := by
  have h1 : (s : G) * u * (s : G)⁻¹ ∈ W := h ▸ v.2
  have e : v = ⟨_, h1⟩ := Subtype.ext h.symm
  rw [e, F.equiv s u h1]

variable [Finite G]

namespace Setting

variable {T M L W : Subgroup G} {F : S5Frame (L ⊔ T) W} {n : ℕ}

omit [Finite G] in
theorem conj_le_S {X : Subgroup G} (hX : X ≤ baum T) {k : G}
    (hk : k ∈ Subgroup.normalizer (baum T : Set G)) :
    X.map (MulAut.conj k).toMonoidHom ≤ baum T := by
  rw [conj_map_le_iff]
  intro x hx
  exact (Subgroup.mem_normalizer_iff.mp hk x).mp (hX hx)

theorem S_le_normalizer_W (hs : Setting T M L W F n) :
    baum T ≤ Subgroup.normalizer (W : Set G) :=
  (S_le_T T).trans (le_sup_right.trans hs.sup_le_normalizer)

theorem S_le_normalizer_QC (hs : Setting T M L W F n) :
    baum T ≤ Subgroup.normalizer
      ((baum T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  have key : ∀ s ∈ baum T, ∀ c ∈ baum T ⊓ Subgroup.centralizer (L : Set G),
      s * c * s⁻¹ ∈ baum T ⊓ Subgroup.centralizer (L : Set G) := by
    intro s hsS c hc
    refine Subgroup.mem_inf.mpr
      ⟨(baum T).mul_mem ((baum T).mul_mem hsS hc.1) ((baum T).inv_mem hsS), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hsL := hs.hyp.T_le_normalizer (S_le_T T hsS)
    have hl' : s⁻¹ * l * s ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsL) l).mp hl
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hl'
    calc l * (s * c * s⁻¹) = s * ((s⁻¹ * l * s) * c) * s⁻¹ := by group
      _ = s * (c * (s⁻¹ * l * s)) * s⁻¹ := by rw [h1]
      _ = s * c * s⁻¹ * l := by group
  intro s hsS
  refine mem_normalizer_of_conj (key s hsS) fun c hc => ?_
  have := key s⁻¹ ((baum T).inv_mem hsS) c hc
  simpa using this

omit [Finite G] in
theorem S_le_normalizer_conj {X : Subgroup G}
    (hX : baum T ≤ Subgroup.normalizer (X : Set G)) {k : G}
    (hk : k ∈ Subgroup.normalizer (baum T : Set G)) :
    baum T ≤ Subgroup.normalizer ((X.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G) := by
  have key : ∀ s ∈ baum T, ∀ x ∈ X.map (MulAut.conj k).toMonoidHom,
      s * x * s⁻¹ ∈ X.map (MulAut.conj k).toMonoidHom := by
    intro s hsS x hx
    rw [mem_conj_map] at hx ⊢
    have hs' : k⁻¹ * s * k ∈ baum T := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) s).mp hsS
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (hX hs') _).mp hx
    have e : k⁻¹ * (s * x * s⁻¹) * k =
        (k⁻¹ * s * k) * (k⁻¹ * x * k) * (k⁻¹ * s * k)⁻¹ := by group
    rw [e]
    exact h1
  intro s hsS
  refine mem_normalizer_of_conj (key s hsS) fun x hx => ?_
  have := key s⁻¹ ((baum T).inv_mem hsS) x hx
  simpa using this

theorem conj_QC_inf_conj_W (hs : Setting T M L W F n) (k : G) {x : G}
    (h₁ : x ∈ (baum T ⊓ Subgroup.centralizer (L : Set G)).map (MulAut.conj k).toMonoidHom)
    (h₂ : x ∈ W.map (MulAut.conj k).toMonoidHom) : x = 1 := by
  rw [mem_conj_map] at h₁ h₂
  have h3 : k⁻¹ * x * k ∈ W ⊓ (baum T ⊓ Subgroup.centralizer (L : Set G)) := ⟨h₂, h₁⟩
  rw [hs.W_inf_QC, Subgroup.mem_bot] at h3
  have e : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
  rw [e, h3]
  group

theorem isSwap_pair (hs : Setting T M L W F n) {k : G}
    (hk : k ∈ Subgroup.normalizer (baum T : Set G)) (a w : ↥(L ⊔ T))
    (ha : (a : G) ∈ (baum T ⊓ Subgroup.centralizer (L : Set G)).map
      (MulAut.conj k).toMonoidHom)
    (hw : (w : G) ∈ W.map (MulAut.conj k).toMonoidHom) (ha1 : F.ρ a ≠ 1) (hw1 : F.ρ w ≠ 1) :
    (F.ρ a = swap 0 1 ∨ F.ρ a = swap 2 3) ∧ (F.ρ w = swap 0 1 ∨ F.ρ w = swap 2 3) ∧
      F.ρ a ≠ F.ρ w := by
  classical
  have haS : (a : G) ∈ baum T := conj_le_S inf_le_left hk ha
  have hwS : (w : G) ∈ baum T := conj_le_S hs.hB.le_baum hk hw
  have haE : InE4 (F.ρ a) := hs.hB.rho_baum a haS
  have hwE : InE4 (F.ρ w) := hs.hB.rho_baum w hwS
  have hQCn := S_le_normalizer_conj hs.S_le_normalizer_QC hk
  have hWkn := S_le_normalizer_conj hs.S_le_normalizer_W hk
  have hdisj : DisjComm (F.ρ a) (F.ρ w) := by
    intro x y hx hy hxy
    obtain ⟨u, rfl⟩ := F.c_surj x hx
    obtain ⟨v, rfl⟩ := F.c_surj y hy
    have hau : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (F.le a.2) u).mp u.2) (W.inv_mem u.2)
    have hwv : (w : G) * v * (w : G)⁻¹ * (v : G)⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (F.le w.2) v).mp v.2) (W.inv_mem v.2)
    have hauQ : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ ∈
        (baum T ⊓ Subgroup.centralizer (L : Set G)).map (MulAut.conj k).toMonoidHom := by
      have e : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ = (a : G) * ((u : G) * (a : G)⁻¹ * (u : G)⁻¹) :=
        by group
      rw [e]
      refine Subgroup.mul_mem _ ha ?_
      exact (Subgroup.mem_normalizer_iff.mp (hQCn (hs.hB.le_baum u.2)) _).mp
        (Subgroup.inv_mem _ ha)
    have hwvW : (w : G) * v * (w : G)⁻¹ * (v : G)⁻¹ ∈ W.map (MulAut.conj k).toMonoidHom := by
      have e : (w : G) * v * (w : G)⁻¹ * (v : G)⁻¹ = (w : G) * ((v : G) * (w : G)⁻¹ * (v : G)⁻¹) :=
        by group
      rw [e]
      refine Subgroup.mul_mem _ hw ?_
      exact (Subgroup.mem_normalizer_iff.mp (hWkn (hs.hB.le_baum v.2)) _).mp
        (Subgroup.inv_mem _ hw)
    have h1 := F.c_comm a u hau
    have h2 := F.c_comm w v hwv
    rw [sub_eq_add_vec, sub_eq_add_vec] at hxy
    rw [sub_eq_add_vec]
    have h3 : (⟨_, hau⟩ : ↥W) = ⟨_, hwv⟩ := F.c_inj (by rw [h1, h2, hxy])
    have h3' : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ = (w : G) * v * (w : G)⁻¹ * (v : G)⁻¹ :=
      congrArg Subtype.val h3
    have h4 : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ = 1 :=
      hs.conj_QC_inf_conj_W k hauQ (by rw [h3']; exact hwvW)
    have h5 : (⟨_, hau⟩ : ↥W) = 1 := Subtype.ext h4
    rw [← h1, h5, F.c_one]
  have hsymm : DisjComm (F.ρ w) (F.ρ a) := by
    intro x y hx hy hxy
    have := hdisj y x hy hx hxy.symm
    rw [hxy]
    exact this
  have hne : F.ρ a ≠ F.ρ w := by
    intro heq
    apply ha1
    apply pmv_faithful
    intro x hx
    have h1 := hdisj x x hx hx (by rw [heq])
    exact sub_eq_zero.mp h1
  have hpair : E4Pair (F.ρ a) (F.ρ w) := ⟨haE, hwE, ha1, hw1, hne⟩
  have hpair' : E4Pair (F.ρ w) (F.ρ a) := ⟨hwE, haE, hw1, ha1, hne.symm⟩
  exact ⟨d5_E4_disjoint _ _ hpair hdisj, d5_E4_disjoint _ _ hpair' hsymm, hne⟩

omit [Finite G] in
theorem mem_normalizer_zpowers {x g : G} (h : g * x = x * g) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  have hc : Commute g x := h
  have key : ∀ g' : G, Commute g' x → ∀ y ∈ Subgroup.zpowers x, g' * y * g'⁻¹ ∈
      Subgroup.zpowers x := by
    intro g' hg' y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : g' * x ^ m * g'⁻¹ = x ^ m := by
      rw [(hg'.zpow_right m).eq, mul_inv_cancel_right]
    rw [h1]
    exact Subgroup.zpow_mem_zpowers x m
  refine mem_normalizer_of_conj (key g hc) fun y hy => ?_
  simpa using key g⁻¹ hc.inv_left y hy

theorem QC_conj_le_aux (hs : Setting T M L W F n) {k : G}
    (hk : k ∈ Subgroup.normalizer (baum T : Set G)) (τ τ' π : Perm (Fin 5))
    (u₀ x₀ : Fin 5 → ZMod 2) (hu₀ : ∑ i, u₀ i = 0) (hux : pmv τ u₀ + u₀ = x₀) (hx₀ : x₀ ≠ 0)
    (hπx : pmv π x₀ = x₀) (hπτ : π * τ' * π⁻¹ ≠ τ') (hπ1 : π * τ' * π⁻¹ ≠ 1)
    (a : ↥(L ⊔ T))
    (ha : (a : G) ∈ (baum T ⊓ Subgroup.centralizer (L : Set G)).map
      (MulAut.conj k).toMonoidHom)
    (haτ : F.ρ a = τ)
    (hWk : ∀ v : ↥(L ⊔ T), (v : G) ∈ W.map (MulAut.conj k).toMonoidHom → F.ρ v ≠ 1 →
      F.ρ v = τ')
    (w : ↥(L ⊔ T)) (hw : (w : G) ∈ W.map (MulAut.conj k).toMonoidHom) (hw1 : F.ρ w ≠ 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQCn := S_le_normalizer_conj hs.S_le_normalizer_QC hk
  obtain ⟨x, hxW, hxc, hxQC⟩ : ∃ x : G, ∃ hxW : x ∈ W, F.c ⟨x, hxW⟩ = x₀ ∧
      x ∈ (baum T ⊓ Subgroup.centralizer (L : Set G)).map (MulAut.conj k).toMonoidHom := by
    obtain ⟨u, hu⟩ := F.c_surj u₀ hu₀
    have hau : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (F.le a.2) u).mp u.2) (W.inv_mem u.2)
    refine ⟨_, hau, by rw [F.c_comm a u hau, haτ, hu, hux], ?_⟩
    have e : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ =
        (a : G) * ((u : G) * (a : G)⁻¹ * (u : G)⁻¹) := by group
    rw [e]
    refine Subgroup.mul_mem _ ha ?_
    exact (Subgroup.mem_normalizer_iff.mp (hQCn (hs.hB.le_baum u.2)) _).mp
      (Subgroup.inv_mem _ ha)
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : (⟨x, hxW⟩ : ↥W) = 1 := Subtype.ext h1
    rw [h2, F.c_one] at hxc
    exact hx₀ hxc.symm
  obtain ⟨y, hy⟩ := F.ρ_surj π
  have hyx : (y : G) * x * (y : G)⁻¹ = x := by
    have hyx' : (y : G) * x * (y : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (F.le y.2) x).mp hxW
    have h1 := F.equiv y ⟨x, hxW⟩ hyx'
    rw [hy, hxc, hπx, ← hxc] at h1
    exact congrArg Subtype.val (F.c_inj h1)
  rw [mem_conj_map] at hxQC
  set x' := k⁻¹ * x * k with hx'
  have hx'1 : x' ≠ 1 := by
    intro h1
    apply hx1
    have e : x = k * x' * k⁻¹ := by rw [hx']; group
    rw [e, h1]
    group
  have hC : Subgroup.zpowers x' ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hx'1
  have hC2 : IsPGroup 2 (Subgroup.zpowers x') :=
    hs.hyp.sylow.1.to_le (Subgroup.zpowers_le.mpr (S_le_T T hxQC.1))
  have hLC : L ≤ Subgroup.normalizer ((Subgroup.zpowers x' : Subgroup G) : Set G) :=
    fun l hl => mem_normalizer_zpowers (Subgroup.mem_centralizer_iff.mp hxQC.2 l hl)
  have hNM := hs.hyp.normalizer_le_of_le hs.h432 hC hC2 hLC
  have hy'x' : (k⁻¹ * y * k) * x' = x' * (k⁻¹ * y * k) := by
    have e1 : (k⁻¹ * y * k) * x' = k⁻¹ * ((y : G) * x * (y : G)⁻¹) * y * k := by
      rw [hx']; group
    rw [e1, hyx, hx']
    group
  have hy'M : k⁻¹ * y * k ∈ M := hNM (mem_normalizer_zpowers hy'x')
  have hy'W := hs.M_le_normalizer hy'M
  have hyWk : ∀ v ∈ W.map (MulAut.conj k).toMonoidHom,
      (y : G) * v * (y : G)⁻¹ ∈ W.map (MulAut.conj k).toMonoidHom := by
    intro v hv
    rw [mem_conj_map] at hv ⊢
    have h1 := (Subgroup.mem_normalizer_iff.mp hy'W _).mp hv
    have e : k⁻¹ * ((y : G) * v * (y : G)⁻¹) * k =
        (k⁻¹ * y * k) * (k⁻¹ * v * k) * (k⁻¹ * y * k)⁻¹ := by group
    rw [e]
    exact h1
  have hwτ : F.ρ w = τ' := hWk w hw hw1
  have hw' : ((y * w * y⁻¹ : ↥(L ⊔ T)) : G) ∈ W.map (MulAut.conj k).toMonoidHom :=
    hyWk _ hw
  have hρw' : F.ρ (y * w * y⁻¹) = π * τ' * π⁻¹ := by
    rw [map_mul, map_mul, map_inv, hy, hwτ]
  by_cases h1 : F.ρ (y * w * y⁻¹) = 1
  · exact hπ1 (hρw'.symm.trans h1)
  · exact hπτ (hρw'.symm.trans (hWk _ hw' h1))

theorem QC_conj_le (hs : Setting T M L W F n) {k : G}
    (hk : k ∈ Subgroup.normalizer (baum T : Set G))
    (hkW : ¬ W.map (MulAut.conj k).toMonoidHom ≤ baum T ⊓ Subgroup.centralizer (W : Set G)) :
    (baum T ⊓ Subgroup.centralizer (L : Set G)).map (MulAut.conj k).toMonoidHom ≤
      baum T ⊓ Subgroup.centralizer (W : Set G) := by
  classical
  by_contra hQC
  obtain ⟨a₀, ha₀, ha₀Q⟩ := Set.not_subset.mp hQC
  obtain ⟨w₀, hw₀, hw₀Q⟩ := Set.not_subset.mp hkW
  have ha₀S : a₀ ∈ baum T := conj_le_S inf_le_left hk ha₀
  have hw₀S : w₀ ∈ baum T := conj_le_S hs.hB.le_baum hk hw₀
  set a : ↥(L ⊔ T) := ⟨a₀, Subgroup.mem_sup_right (S_le_T T ha₀S)⟩ with ha
  set w : ↥(L ⊔ T) := ⟨w₀, Subgroup.mem_sup_right (S_le_T T hw₀S)⟩ with hw
  have ha1 : F.ρ a ≠ 1 := fun h1 => ha₀Q ((hs.rho_eq_one_iff a ha₀S).1 h1)
  have hw1 : F.ρ w ≠ 1 := fun h1 => hw₀Q ((hs.rho_eq_one_iff w hw₀S).1 h1)
  obtain ⟨hasw, -, -⟩ := hs.isSwap_pair hk a w ha₀ hw₀ ha1 hw1
  have hWk : ∀ τ' : Perm (Fin 5), (F.ρ a = swap 0 1 → τ' = swap 2 3) →
      (F.ρ a = swap 2 3 → τ' = swap 0 1) →
      ∀ v : ↥(L ⊔ T), (v : G) ∈ W.map (MulAut.conj k).toMonoidHom → F.ρ v ≠ 1 →
        F.ρ v = τ' := by
    intro τ' h01 h23 v hv hv1
    obtain ⟨-, h2, h3⟩ := hs.isSwap_pair hk a v ha₀ hv ha1 hv1
    rcases hasw with h | h <;> rcases h2 with h' | h'
    · exact absurd (h.trans h'.symm) h3
    · rw [h', h01 h]
    · rw [h', h23 h]
    · exact absurd (h.trans h'.symm) h3
  rcases hasw with h | h
  · exact hs.QC_conj_le_aux hk (swap 0 1) (swap 2 3) (swap 2 4) ![1, 0, 0, 0, 1]
      ![1, 1, 0, 0, 0] (by decide) (by decide) (by decide) d5_stab_01.1 d5_stab_01.2.1
      d5_stab_01.2.2 a ha₀ h (hWk _ (fun _ => rfl) fun h' => absurd (h.symm.trans h')
        (by decide)) w hw₀ hw1
  · exact hs.QC_conj_le_aux hk (swap 2 3) (swap 0 1) (swap 0 4) ![0, 0, 1, 0, 1]
      ![0, 0, 1, 1, 0] (by decide) (by decide) (by decide) d5_stab_23.1 d5_stab_23.2.1
      d5_stab_23.2.2 a ha₀ h (hWk _ (fun h' => absurd (h.symm.trans h') (by decide))
        fun _ => rfl) w hw₀ hw1

end Setting

end CFSG.Quasithin.H13.A5Push
