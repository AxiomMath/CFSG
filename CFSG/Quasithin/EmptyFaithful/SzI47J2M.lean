module

public import CFSG.Quasithin.EmptyFaithful.SzI47J2Steps
public import CFSG.Quasithin.EmptyFaithful.SzI47J2MAut

public section

namespace CFSG.Quasithin.SzI47J2M

open CFSG.Open CFSG.QuasithinUnique

theorem nonempty_alt_of_centralizer {Y : Type} [Group Y] [Finite Y] {z s : Y}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hs2 : s * s = 1) (hs1 : s ≠ 1) (hsz : s ≠ z)
    (hzs : z * s = s * z)
    (hC : ∀ g : Y, g * z = z * g → g = 1 ∨ g = z ∨ g = s ∨ g = z * s)
    (hinv : ∀ u : Y, u * u = 1 → u ≠ 1 → ∃ g : Y, g * u * g⁻¹ = z) :
    Nonempty (Y ≃* alternatingGroup (Fin 4)) ∨ Nonempty (Y ≃* alternatingGroup (Fin 5)) := by
  have hto : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hzt : ∀ x ∈ Subgroup.zpowers z, x = 1 ∨ x = z := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hto]
    have h0 : 0 ≤ k % ((2 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h2 : k % ((2 : ℕ) : ℤ) < 2 := Int.emod_lt_of_pos _ (by norm_num)
    rcases (by omega : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1) with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hto]
  have hsK : s ∉ Subgroup.zpowers z := fun h1 => by
    rcases hzt s h1 with h2 | h2
    · exact hs1 h2
    · exact hsz h2
  have hzC : z ∈ Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hsC : s ∈ Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzs.symm
  have hjoin : Subgroup.centralizer ({z} : Set Y) = Subgroup.zpowers z ⊔ Subgroup.zpowers s := by
    apply le_antisymm
    · intro g hg
      rcases hC g (Subgroup.mem_centralizer_singleton_iff.mp hg) with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · exact sup_le (Subgroup.zpowers_le.mpr hzC) (Subgroup.zpowers_le.mpr hsC)
  have hdisj : ∀ g : Y, g ∉ Subgroup.centralizer ({z} : Set Y) →
      Disjoint (Subgroup.zpowers z) ((Subgroup.zpowers z).conjBy g) := by
    intro g hg
    rw [Subgroup.disjoint_def]
    intro x hx hxg
    rcases hzt x hx with hx1 | hxt
    · exact hx1
    · exfalso
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxg
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      rw [hxt] at hyx
      rcases hzt y hy with hy1 | hyt
      · apply hz1
        rw [← hyx, hy1]
        group
      · apply hg
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [hyt] at hyx
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := by rw [hyx]
  let h : CFSG.GorensteinWalter.BrauerSuzukiWallHypotheses Y :=
    { t := z
      K := Subgroup.zpowers z
      H := Subgroup.centralizer ({z} : Set Y)
      s := s
      t_involution := ⟨hz1, by rw [pow_two]; exact hz2⟩
      t_mem_K := Subgroup.mem_zpowers z
      H_eq_centralizer := rfl
      K_commutative := inferInstance
      s_involution := ⟨hs1, by rw [pow_two]; exact hs2⟩
      s_not_mem_K := hsK
      H_eq_join := hjoin
      fixed_subgroup_eq :=
        inf_eq_left.mpr (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hzs))
      s_inverts_K := fun x hx => by
        rcases hzt x hx with rfl | rfl
        · group
        · rw [← hzs, mul_inv_cancel_right]
          exact (inv_eq_of_mul_eq_one_right hz2).symm
      conjugate_disjoint := hdisj
      involutions_conjugate := fun u hu => hinv u (by rw [← pow_two]; exact hu.2) hu.1 }
  have hk : Nat.card h.K = 2 := hzcard
  by_cases hNtop : Subgroup.normalizer (h.H : Set Y) = ⊤
  · obtain ⟨e4⟩ := h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
    exact Or.inl ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hNtop.symm)).trans e4⟩
  · exact Or.inr (h.mulEquiv_alternatingGroup_five_of_card_K_eq_two_of_normalizer_ne_top hk hNtop)

theorem kernelAlt : J2KernelAlt := by
  intro G _ _ z hcount F
  have hzM := F.W_le_M hcount F.z_mem_W
  have hx4M := F.W_le_M hcount F.pt_four_mem_W
  have hzz := F.mul_self_of_mem_W F.z_mem_W
  have hx4x4 := F.mul_self_of_mem_W F.pt_four_mem_W
  have hx4ne : F.pt 4 ≠ 1 := fun h1 =>
    J2Cz.QM.x_ne_one 4 (F.emb_injective (h1.trans (map_one F.emb).symm))
  have hx4z : F.pt 4 ≠ z := fun h1 =>
    J2Cz.QM.x_ne_z 4 (F.emb_injective (h1.trans F.emb_z.symm))
  refine nonempty_alt_of_centralizer (z := ⟨z, hzM⟩) (s := ⟨F.pt 4, hx4M⟩)
    (Subtype.ext hzz) (fun h1 => F.isTypeH2.ne_one (congrArg Subtype.val h1))
    (Subtype.ext hx4x4) (fun h1 => hx4ne (congrArg Subtype.val h1))
    (fun h1 => hx4z (congrArg Subtype.val h1))
    (Subtype.ext (F.comm_of_mem_W F.z_mem_W F.pt_four_mem_W)) ?_ ?_
  · intro g hg
    have hgW := F.mem_W_of_mem_M hcount g.2 (congrArg Subtype.val hg)
    rcases F.mem_W.mp hgW with h1 | h1 | h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Or.inl (Subtype.ext h1))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h1)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h1)))
  · intro u hu hu1
    obtain ⟨m, hmM, hm⟩ := F.exists_mem_M_conj_eq_z hcount u.2 (congrArg Subtype.val hu)
      (fun h1 => hu1 (Subtype.ext h1))
    exact ⟨⟨m, hmM⟩, Subtype.ext hm⟩

def conjOn {G : Type} [Group G] (N : Subgroup G) (g : G) (h₁ : ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (h₂ : ∀ n ∈ N, g⁻¹ * n * g ∈ N) : MulAut ↥N where
  toFun n := ⟨g * n * g⁻¹, h₁ n n.2⟩
  invFun n := ⟨g⁻¹ * n * g, h₂ n n.2⟩
  left_inv n := Subtype.ext (by
    show g⁻¹ * (g * (n : G) * g⁻¹) * g = n
    group)
  right_inv n := Subtype.ext (by
    show g * (g⁻¹ * (n : G) * g) * g⁻¹ = n
    group)
  map_mul' x y := Subtype.ext (by
    show g * ((x : G) * y) * g⁻¹ = g * (x : G) * g⁻¹ * (g * (y : G) * g⁻¹)
    group)

section Frame

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_mem_W_conj_eq (hcount : involutionClassCount G = 2) (F : J2Frame G z) :
    ∃ u ∈ F.W, ∀ m ∈ F.M hcount, F.a * m * F.a⁻¹ = u * m * u⁻¹ := by
  have hzM := F.W_le_M hcount F.z_mem_W
  have hx4M := F.W_le_M hcount F.pt_four_mem_W
  have hzz := F.mul_self_of_mem_W F.z_mem_W
  have hx4x4 := F.mul_self_of_mem_W F.pt_four_mem_W
  have hx4ne : F.pt 4 ≠ 1 := fun h1 =>
    J2Cz.QM.x_ne_one 4 (F.emb_injective (h1.trans (map_one F.emb).symm))
  have hx4z : F.pt 4 ≠ z := fun h1 =>
    J2Cz.QM.x_ne_z 4 (F.emb_injective (h1.trans F.emb_z.symm))
  let α : MulAut ↥(F.M hcount) := conjOn (F.M hcount) F.a
    (fun m hm => F.conj_mem_M hcount hm F.a_mem_X)
    (fun m hm => by simpa using F.conj_mem_M hcount hm (F.X.inv_mem F.a_mem_X))
  have hαz : α ⟨z, hzM⟩ = ⟨z, hzM⟩ := Subtype.ext (by
    show F.a * z * F.a⁻¹ = z
    rw [F.comm_of_mem_T F.a_mem_T (F.W_le_T F.z_mem_W), mul_inv_cancel_right])
  have hαx : α ⟨F.pt 4, hx4M⟩ = ⟨F.pt 4, hx4M⟩ := Subtype.ext (by
    show F.a * F.pt 4 * F.a⁻¹ = F.pt 4
    rw [F.comm_of_mem_T F.a_mem_T (F.W_le_T F.pt_four_mem_W), mul_inv_cancel_right])
  obtain ⟨u, hu, hα⟩ := exists_inner_of_fixes_klein (kernelAlt G z hcount F)
    (v₁ := ⟨z, hzM⟩) (v₂ := ⟨F.pt 4, hx4M⟩) (Subtype.ext hzz) (Subtype.ext hx4x4)
    (fun h1 => F.isTypeH2.ne_one (congrArg Subtype.val h1))
    (fun h1 => hx4ne (congrArg Subtype.val h1))
    (fun h1 => hx4z (congrArg Subtype.val h1).symm)
    (Subtype.ext (F.comm_of_mem_W F.z_mem_W F.pt_four_mem_W)) α hαz hαx
  have huW : (u : G) ∈ F.W := by
    rcases hu with rfl | rfl | rfl | rfl
    · exact F.W.one_mem
    · exact F.z_mem_W
    · exact F.pt_four_mem_W
    · exact F.W.mul_mem F.z_mem_W F.pt_four_mem_W
  exact ⟨u, huW, fun m hm => congrArg Subtype.val (hα ⟨m, hm⟩)⟩

theorem exists_mem_T_comm_M (hcount : involutionClassCount G = 2) (F : J2Frame G z) :
    ∃ r ∈ F.T, ∃ u ∈ F.W, F.a = u * r ∧ ∀ m ∈ F.M hcount, r * m = m * r := by
  obtain ⟨u, huW, hu⟩ := exists_mem_W_conj_eq hcount F
  refine ⟨u⁻¹ * F.a, F.T.mul_mem (F.T.inv_mem (F.W_le_T huW)) F.a_mem_T, u, huW, by group,
    fun m hm => ?_⟩
  calc u⁻¹ * F.a * m = u⁻¹ * (F.a * m * F.a⁻¹) * F.a := by group
    _ = u⁻¹ * (u * m * u⁻¹) * F.a := by rw [hu m hm]
    _ = m * (u⁻¹ * F.a) := by group

end Frame

section Klein

variable {G : Type} [Group G] {s r : G}

def kleinOf (s r : G) (hs : s * s = 1) (hr : r * r = 1) (hsr : s * r = r * s) : Subgroup G where
  carrier := {x | x = 1 ∨ x = s ∨ x = r ∨ x = s * r}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    have e1 : s * (s * r) = r := by rw [← mul_assoc, hs, one_mul]
    have e2 : r * s = s * r := hsr.symm
    have e3 : r * (s * r) = s := by rw [hsr, ← mul_assoc, hr, one_mul]
    have e4 : s * r * s = r := by rw [mul_assoc, ← hsr, ← mul_assoc, hs, one_mul]
    have e5 : s * r * r = s := by rw [mul_assoc, hr, mul_one]
    have e6 : s * r * (s * r) = 1 := by rw [← mul_assoc, e4, hr]
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
      simp [hx, hy, hs, hr, e1, e2, e3, e4, e5, e6]
  inv_mem' := by
    intro x hx
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rcases hx with hx | hx | hx | hx
    · left
      rw [hx, inv_one]
    · right; left
      rw [hx, hsi]
    · right; right; left
      rw [hx, hri]
    · right; right; right
      rw [hx, mul_inv_rev, hsi, hri, hsr]

theorem mem_kleinOf {hs : s * s = 1} {hr : r * r = 1} {hsr : s * r = r * s} {x : G} :
    x ∈ kleinOf s r hs hr hsr ↔ x = 1 ∨ x = s ∨ x = r ∨ x = s * r :=
  Iff.rfl

theorem mul_self_of_mem_kleinOf {hs : s * s = 1} {hr : r * r = 1} {hsr : s * r = r * s} {x : G}
    (hx : x ∈ kleinOf s r hs hr hsr) : x * x = 1 := by
  have e4 : s * r * s = r := by rw [mul_assoc, ← hsr, ← mul_assoc, hs, one_mul]
  rcases mem_kleinOf.mp hx with rfl | rfl | rfl | rfl
  · exact one_mul 1
  · exact hs
  · exact hr
  · rw [← mul_assoc, e4, hr]

theorem kleinOf_le {hs : s * s = 1} {hr : r * r = 1} {hsr : s * r = r * s} {S : Subgroup G}
    (hsS : s ∈ S) (hrS : r ∈ S) : kleinOf s r hs hr hsr ≤ S := by
  intro x hx
  rcases mem_kleinOf.mp hx with rfl | rfl | rfl | rfl
  · exact S.one_mem
  · exact hsS
  · exact hrS
  · exact S.mul_mem hsS hrS

theorem comm_of_mem_kleinOf {hs : s * s = 1} {hr : r * r = 1} {hsr : s * r = r * s} {x m : G}
    (hx : x ∈ kleinOf s r hs hr hsr) (hsm : s * m = m * s) (hrm : r * m = m * r) :
    x * m = m * x := by
  rcases mem_kleinOf.mp hx with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact hsm
  · exact hrm
  · calc s * r * m = s * (r * m) := by rw [mul_assoc]
      _ = s * (m * r) := by rw [hrm]
      _ = (s * m) * r := by rw [mul_assoc]
      _ = (m * s) * r := by rw [hsm]
      _ = m * (s * r) := by rw [mul_assoc]

theorem card_kleinOf (hs : s * s = 1) (hr : r * r = 1) (hsr : s * r = r * s) (hs1 : s ≠ 1)
    (hr1 : r ≠ 1) (hsr' : s ≠ r) : Nat.card (kleinOf s r hs hr hsr) = 4 := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have h1 : s * r ≠ 1 := fun h => hsr' (by
    calc s = s * r * r⁻¹ := by group
      _ = r := by rw [h, hri, one_mul])
  have h2 : s ≠ s * r := fun h => hr1 (by
    have h3 : s * 1 = s * r := by rw [mul_one]; exact h
    exact (mul_left_cancel h3).symm)
  have h3 : r ≠ s * r := fun h => hs1 (by
    have h4 : 1 * r = s * r := by rw [one_mul]; exact h
    exact (mul_right_cancel h4).symm)
  have hset : ((kleinOf s r hs hr hsr : Subgroup G) : Set G) = {1, s, r, s * r} := rfl
  calc Nat.card (kleinOf s r hs hr hsr)
      = Set.ncard ((kleinOf s r hs hr hsr : Subgroup G) : Set G) := Nat.card_coe_set_eq _
    _ = Set.ncard ({1, s, r, s * r} : Set G) := by rw [hset]
    _ = 4 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
        Set.ncard_singleton]
      · simpa using h3
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hsr', h2⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hs1.symm, hr1.symm, h1.symm⟩

end Klein

theorem kernelComplementExists : J2KernelComplementExists := by
  intro G _ _ z hcount F
  obtain ⟨r, hrT, u, huW, hau, hrM⟩ := exists_mem_T_comm_M hcount F
  have huT := F.W_le_T huW
  have htu : F.t * u = u * F.t := F.comm_of_mem_T F.t_mem_T huT
  have hru : r * u = u * r := F.comm_of_mem_T hrT huT
  have hrr : r * r = 1 := F.mul_self_of_mem_T hrT
  have htr : F.t * r = r * F.t := F.comm_of_mem_T F.t_mem_T hrT
  have hrW : r ∉ F.W := fun h => F.a_not_mem_W (by rw [hau]; exact F.W.mul_mem huW h)
  have htrW : F.t * r ∉ F.W := fun h => F.ta_not_mem_W (by
    have e : F.t * F.a = u * (F.t * r) := by
      calc F.t * F.a = F.t * (u * r) := by rw [hau]
        _ = (F.t * u) * r := by rw [mul_assoc]
        _ = (u * F.t) * r := by rw [htu]
        _ = u * (F.t * r) := by rw [mul_assoc]
    rw [e]
    exact F.W.mul_mem huW h)
  have hr1 : r ≠ 1 := fun h => hrW (h ▸ F.W.one_mem)
  have htr' : F.t ≠ r := fun h => htrW (by
    rw [← h, F.t_mul_t]
    exact F.W.one_mem)
  refine ⟨kleinOf F.t r F.t_mul_t hrr htr, ?_⟩
  have hR1 : F.t ∈ kleinOf F.t r F.t_mul_t hrr htr := Or.inr (Or.inl rfl)
  have hR2 : r ∈ kleinOf F.t r F.t_mul_t hrr htr := Or.inr (Or.inr (Or.inl rfl))
  have hR3 : F.t * r ∈ kleinOf F.t r F.t_mul_t hrr htr := Or.inr (Or.inr (Or.inr rfl))
  have hle : kleinOf F.t r F.t_mul_t hrr htr ≤ F.T := kleinOf_le F.t_mem_T hrT
  refine
    { t_mem := hR1
      card := card_kleinOf F.t_mul_t hrr htr F.t_ne_one hr1 htr'
      mul_self := fun x hx => mul_self_of_mem_kleinOf hx
      le_T := hle
      comm_M := fun x hx m hm => comm_of_mem_kleinOf hx
        (F.mem_X.mp (F.M_le_X hcount hm)).symm (hrM m hm)
      inf_W := ?_
      X_eq := ?_ }
  · rw [eq_bot_iff]
    rintro x ⟨hxR, hxW⟩
    rcases mem_kleinOf.mp hxR with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hxW F.t_not_mem_W
    · exact absurd hxW hrW
    · exact absurd hxW htrW
  · intro g hg
    obtain ⟨s, hsT, hgs⟩ := F.exists_mem_T_mul_inv_mem_M hcount hg
    obtain ⟨l, hl, w, hw, hsw⟩ := F.exists_eq_mul_of_mem_T hsT
    have hdec : ∃ ρ ∈ kleinOf F.t r F.t_mul_t hrr htr, ∃ w' ∈ F.W, s = ρ * w' := by
      rw [hsw]
      rcases hl with rfl | rfl | rfl | rfl
      · exact ⟨1, Subgroup.one_mem _, w, hw, rfl⟩
      · exact ⟨F.t, hR1, w, hw, rfl⟩
      · refine ⟨r, hR2, u * w, F.W.mul_mem huW hw, ?_⟩
        rw [hau, ← mul_assoc r u w, hru]
      · refine ⟨F.t * r, hR3, u * w, F.W.mul_mem huW hw, ?_⟩
        calc F.t * F.a * w = F.t * (u * r) * w := by rw [hau]
          _ = F.t * ((u * r) * w) := by rw [mul_assoc]
          _ = F.t * ((r * u) * w) := by rw [hru]
          _ = F.t * r * (u * w) := by group
    obtain ⟨ρ, hρ, w', hw', hs⟩ := hdec
    have hρw' : ρ * w' = w' * ρ := F.comm_of_mem_T (hle hρ) (F.W_le_T hw')
    refine ⟨g * s⁻¹ * w', (F.M hcount).mul_mem hgs (F.W_le_M hcount hw'), ρ, hρ, ?_⟩
    rw [hs]
    calc g = g * (ρ * w')⁻¹ * (w' * ρ) := by rw [← hρw']; group
      _ = g * (ρ * w')⁻¹ * w' * ρ := by group

end CFSG.Quasithin.SzI47J2M

namespace CFSG.Quasithin

theorem j2KernelAlt_holds : J2KernelAlt := SzI47J2M.kernelAlt

theorem j2KernelComplementExists_holds : J2KernelComplementExists :=
  SzI47J2M.kernelComplementExists

end CFSG.Quasithin
