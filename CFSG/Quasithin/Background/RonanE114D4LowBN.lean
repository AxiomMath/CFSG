module

public import CFSG.Quasithin.Vol2.GoldschmidtF431BNPoly
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNYam
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNBase

public section

namespace CFSG.Quasithin.RonanE114Low

open CFSG.GH74.BNPair CFSG.Quasithin CFSG.Quasithin.H13.F431.BN CFSG.Open
  CFSG.LieType.BorelTits
open scoped Pointwise

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

abbrev stab (y : V D) : Subgroup X := MulAction.stabilizer X y

abbrev rad (y : V D) : Subgroup X := pCoreOf 2 (stab D y)

theorem stab_smul (g : X) (y : V D) :
    stab D (g • y) = (stab D y).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g y

theorem rad_smul (g : X) (y : V D) :
    rad D (g • y) = (rad D y).map (MulAut.conj g).toMonoidHom := by
  rw [rad, stab_smul]
  exact pCoreOf_map_mulEquiv 2 (MulAut.conj g) _

theorem stab_v (i : Bool) : stab D (v D i) = P D i := stabilizer_v_eq D i

theorem rad_v (i : Bool) : rad D (v D i) = Q D i := by
  rw [rad, stab_v]
  rfl

theorem smul_v_eq_iff (g : X) (i : Bool) : g • v D i = v D i ↔ g ∈ P D i := by
  rw [← MulAction.mem_stabilizer_iff, stabilizer_v_eq]

theorem mem_rad_smul_iff {g x : X} {y : V D} : x ∈ rad D (g • y) ↔ g⁻¹ * x * g ∈ rad D y := by
  rw [rad_smul, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem mem_stab_smul_iff {g x : X} {y : V D} : x ∈ stab D (g • y) ↔ g⁻¹ * x * g ∈ stab D y := by
  rw [stab_smul, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem exists_smul_v (y : V D) : ∃ (g : X) (i : Bool), y = g • v D i := by
  obtain ⟨i, x, hx⟩ := exists_vtx y
  refine ⟨x⁻¹, i, ?_⟩
  rw [v_eq_vt, smul_vt, inv_inv, one_mul]
  exact hx

theorem vtype_smul_v (g : X) (i : Bool) : vtype D.B D.N D.w₁ D.w₂ (g • v D i) = i := by
  rw [v_eq_vt, smul_vt]
  exact vtype_vt D i _

theorem even_dist_smul_v (g h : X) (i : Bool) : Even ((Γ D).dist (g • v D i) (h • v D i)) := by
  have hc := (GPath.dist_even_iff (isGenPolygon D).connected (adj_iff_vtype D)
    (g • v D i) (h • v D i)).1
  exact hc (by rw [vtype_smul_v, vtype_smul_v])

theorem odd_dist_smul_v (g h : X) : Odd ((Γ D).dist (g • v D true) (h • v D false)) := by
  have hc := GPath.dist_even_iff (isGenPolygon D).connected (adj_iff_vtype D)
    (g • v D true) (h • v D false)
  rw [vtype_smul_v, vtype_smul_v] at hc
  exact Nat.not_even_iff_odd.mp fun h' => absurd (hc.2 h') (by decide)

theorem dist_le (y z : V D) : (Γ D).dist y z ≤ n := (isGenPolygon D).diam_le y z

theorem fix_of_geodesic {k : ℕ} (hk : k < n) (p : GPath (Γ D) k)
    (hp : (Γ D).dist (p 0) (p k) = k) {g : X} (h0 : g • p 0 = p 0) (hk' : g • p k = p k)
    {i : ℕ} (hi : i ≤ k) : g • p i = p i := by
  have hgeo : (g • p).IsGeodesic := by
    show (Γ D).dist ((g • p) 0) ((g • p) k) = k
    rw [GPath.smul_apply, GPath.smul_apply, h0, hk', hp]
  have heq := (isGenPolygon D).uniqueGeod k (g • p) p hgeo hp (by rw [GPath.smul_apply, h0])
    (by rw [GPath.smul_apply, hk']) hk
  have := congrArg (fun q : GPath (Γ D) k => q i) heq
  simpa using this

theorem nbr_true {e : V D} (h : (Γ D).Adj (v D true) e) :
    e = v D false ∨ ∃ x ∈ D.root 1, e = (x * mi D true) • v D false := by
  obtain ⟨p, hp, rfl⟩ := flag_true D e h
  rw [← P_true] at hp
  rcases (mem_P_iff D).1 hp with hB | hd
  · exact Or.inl ((smul_v_eq_iff D p false).2 (B_le_P D false hB))
  · right
    have hw : gen D.w₁ D.w₂ true = D.w₁ := rfl
    rw [hw] at hd
    set m₀ : D.N := D.lift (gen D.w₁ D.w₂ true) with hm₀
    have hm₀w : ((m₀ : D.N) : D.Weyl) = D.w₁ := D.lift_mk _
    have hm₁w : ((m₀⁻¹ : D.N) : D.Weyl) = D.w₁ := D.inv_lift₁ m₀ hm₀w
    obtain ⟨b, hb, b', hb', rfl⟩ := (mem_dc_of_lift hm₀w).1 hd
    have hpinv : (b * (m₀ : X) * b')⁻¹ ∈ dc D.B D.N D.w₁ := by
      refine (mem_dc_of_lift hm₁w).2 ⟨b'⁻¹, D.B.inv_mem hb', b⁻¹, D.B.inv_mem hb, ?_⟩
      simp [mul_assoc]
    obtain ⟨b₀, hb₀, x, hx, hpx⟩ := D.dc_panel_w₁ m₀⁻¹ hm₁w hpinv
    refine ⟨x⁻¹, (D.root 1).inv_mem hx, ?_⟩
    have hp : b * (m₀ : X) * b' = (x⁻¹ * mi D true) * b₀⁻¹ := by
      have e1 : b * (m₀ : X) * b' = (b₀ * ((m₀⁻¹ : D.N) : X) * x)⁻¹ := by rw [← hpx, inv_inv]
      rw [e1]
      simp [mi, hm₀, mul_assoc]
    rw [hp, mul_smul, (smul_v_eq_iff D _ false).2 (B_le_P D false (D.B.inv_mem hb₀))]

theorem nbr_false {e : V D} (h : (Γ D).Adj (v D false) e) :
    e = v D true ∨ ∃ x ∈ D.root n, e = (x * mi D false) • v D true := by
  obtain ⟨p, hp, rfl⟩ := flag_false D e h
  rw [← P_false] at hp
  rcases (mem_P_iff D).1 hp with hB | hd
  · exact Or.inl ((smul_v_eq_iff D p true).2 (B_le_P D true hB))
  · right
    have hw : gen D.w₁ D.w₂ false = D.w₂ := rfl
    rw [hw] at hd
    set m₀ : D.N := D.lift (gen D.w₁ D.w₂ false) with hm₀
    have hm₀w : ((m₀ : D.N) : D.Weyl) = D.w₂ := D.lift_mk _
    have hm₁w : ((m₀⁻¹ : D.N) : D.Weyl) = D.w₂ := D.inv_lift₂ m₀ hm₀w
    obtain ⟨b, hb, b', hb', rfl⟩ := (mem_dc_of_lift hm₀w).1 hd
    have hpinv : (b * (m₀ : X) * b')⁻¹ ∈ dc D.B D.N D.w₂ := by
      refine (mem_dc_of_lift hm₁w).2 ⟨b'⁻¹, D.B.inv_mem hb', b⁻¹, D.B.inv_mem hb, ?_⟩
      simp [mul_assoc]
    obtain ⟨b₀, hb₀, x, hx, hpx⟩ := D.dc_panel_w₂ m₀⁻¹ hm₁w hpinv
    refine ⟨x⁻¹, (D.root n).inv_mem hx, ?_⟩
    have hp : b * (m₀ : X) * b' = (x⁻¹ * mi D false) * b₀⁻¹ := by
      have e1 : b * (m₀ : X) * b' = (b₀ * ((m₀⁻¹ : D.N) : X) * x)⁻¹ := by rw [← hpx, inv_inv]
      rw [e1]
      simp [mi, hm₀, mul_assoc]
    rw [hp, mul_smul, (smul_v_eq_iff D _ true).2 (B_le_P D true (D.B.inv_mem hb₀))]

theorem adj_true_of_mem {p : X} (hp : p ∈ P D true) : (Γ D).Adj (v D true) (p • v D false) :=
  (adj_v_true_iff D).2 ⟨p, hp, rfl⟩

section Finite

variable [Finite X] (hU : CFSG.QuasithinUnique.IsSylowTwoOf D.U ⊤)
include hU

theorem le_U_of_le_B {R : Subgroup X} (hRB : R ≤ D.B) (hR2 : IsPGroup 2 R) : R ≤ D.U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ D.U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  let S : Sylow 2 X := hU.2.1.toSylow hidx
  have hsup : IsPGroup 2 (R ⊔ D.U : Subgroup X) :=
    hR2.to_sup_of_normal_right' hU.2.1 (hRB.trans (B_le_normalizer_U D))
  have := S.is_maximal' hsup (le_sup_right : D.U ≤ R ⊔ D.U)
  exact le_sup_left.trans this.le

theorem root_one_inf_Q : D.root 1 ⊓ Q D true = ⊥ := by
  rw [Q_eq_Uplus D hU true, eq_bot_iff]
  rintro x ⟨hx1, hxQ⟩
  rw [Subgroup.mem_bot]
  have hn := D.three_le
  set m₀ : D.N := D.lift (gen D.w₁ D.w₂ true) with hm₀
  have hm₀w : ((m₀ : D.N) : D.Weyl) = D.w₁ := D.lift_mk _
  have hm₁w : ((m₀⁻¹ : D.N) : D.Weyl) = D.w₁ := D.inv_lift₁ m₀ hm₀w
  have h1 := (D.roots.action₁ (m₀⁻¹) hm₁w).1
  have hmem : (m₀ : X) * x * (m₀ : X)⁻¹ ∈ D.root (-1) := by
    rw [← h1, mem_conjBy_iff]
    simpa [mul_assoc] using hx1
  have hV : (m₀ : X) * x * (m₀ : X)⁻¹ ∈ D.Vm :=
    D.root_le_V D.coe_Vm (by omega) le_rfl hmem
  have hU' : (m₀ : X) * x * (m₀ : X)⁻¹ ∈ D.U := ((mem_Uplus_iff D).1 hxQ).2
  have h2 := D.eq_one_of_mem_U_Vm (D.U_le_B hU') hV
  have h3 : x = (m₀ : X)⁻¹ * ((m₀ : X) * x * (m₀ : X)⁻¹) * (m₀ : X) := by group
  rw [h3, h2]
  group

theorem root_n_inf_Q : D.root n ⊓ Q D false = ⊥ := by
  rw [Q_eq_Uplus D hU false, eq_bot_iff]
  rintro x ⟨hx1, hxQ⟩
  rw [Subgroup.mem_bot]
  have hn := D.three_le
  set m₀ : D.N := D.lift (gen D.w₁ D.w₂ false) with hm₀
  have hm₀w : ((m₀ : D.N) : D.Weyl) = D.w₂ := D.lift_mk _
  have hm₁w : ((m₀⁻¹ : D.N) : D.Weyl) = D.w₂ := D.inv_lift₂ m₀ hm₀w
  have h1 := (D.roots.action₂ (m₀⁻¹) hm₁w).1
  have hmem : (m₀ : X) * x * (m₀ : X)⁻¹ ∈ D.root (-(n : ℤ)) := by
    rw [← h1, mem_conjBy_iff]
    simpa [mul_assoc] using hx1
  have hV : (m₀ : X) * x * (m₀ : X)⁻¹ ∈ D.Vm :=
    D.root_le_V D.coe_Vm le_rfl (by omega) hmem
  have hU' : (m₀ : X) * x * (m₀ : X)⁻¹ ∈ D.U := ((mem_Uplus_iff D).1 hxQ).2
  have h2 := D.eq_one_of_mem_U_Vm (D.U_le_B hU') hV
  have h3 : x = (m₀ : X)⁻¹ * ((m₀ : X) * x * (m₀ : X)⁻¹) * (m₀ : X) := by group
  rw [h3, h2]
  group

theorem le_rad {y w w' : V D} (hw : (Γ D).Adj y w) (hw' : (Γ D).Adj y w') (hne : w ≠ w')
    {R : Subgroup X} (hRy : R ≤ stab D y) (hR2 : IsPGroup 2 R) (hRw : ∀ r ∈ R, r • w = w)
    (hRw' : ∀ r ∈ R, r • w' = w') : R ≤ rad D y := by
  obtain ⟨g, i, rfl⟩ := exists_smul_v D y
  have hadj : ∀ {z : V D}, (Γ D).Adj (g • v D i) z → (Γ D).Adj (v D i) (g⁻¹ • z) := by
    intro z hz
    have := (GraphAction.adj_smul (Γ := Γ D) g⁻¹ (g • v D i) z).2 hz
    rwa [inv_smul_smul] at this
  obtain ⟨z₁, hz₁, hw₁⟩ := exists_nbr D i (hadj hw)
  obtain ⟨z₂, hz₂, hw₂⟩ := exists_nbr D i (hadj hw')
  have hne₁ : vt D (!i) z₁ ≠ vt D (!i) z₂ := by
    rw [← hw₁, ← hw₂]
    exact fun h => hne (smul_left_cancel _ h)
  have hne' : vt D (!i) 1 ≠ vt D (!i) (mi D i) := by
    intro h
    have := (vt_eq_vt_iff (!i) 1 (mi D i)).1 h.symm
    exact mi_not_mem_P_not D i (by simpa [P] using this)
  obtain ⟨h, hh, hh1, hh2⟩ := two_trans D i hz₁ hz₂ (P D i).one_mem (mi_mem_P D i) hne₁ hne'
  set c : X := h * g⁻¹ with hc
  have hcw : ∀ r ∈ R, (c * r * c⁻¹) • vt D (!i) 1 = vt D (!i) 1 := by
    intro r hr
    rw [← hh1, hc, ← hw₁]
    simp only [mul_inv_rev, inv_inv, mul_smul, inv_smul_smul, smul_inv_smul]
    rw [hRw r hr]
  have hcw' : ∀ r ∈ R, (c * r * c⁻¹) • vt D (!i) (mi D i) = vt D (!i) (mi D i) := by
    intro r hr
    rw [← hh2, hc, ← hw₂]
    simp only [mul_inv_rev, inv_inv, mul_smul, inv_smul_smul, smul_inv_smul]
    rw [hRw' r hr]
  have hcP : ∀ r ∈ R, c * r * c⁻¹ ∈ P D i := by
    intro r hr
    have hr' : g⁻¹ * r * g ∈ P D i := by
      rw [← stab_v]
      exact (mem_stab_smul_iff D).1 (hRy hr)
    have e : c * r * c⁻¹ = h * (g⁻¹ * r * g) * h⁻¹ := by rw [hc]; group
    rw [e]
    exact (P D i).mul_mem ((P D i).mul_mem hh hr') ((P D i).inv_mem hh)
  set R' : Subgroup X := R.map (MulAut.conj c).toMonoidHom with hR'
  have hR'2 : IsPGroup 2 R' := hR2.map _
  have hR'B : R' ≤ D.B := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 : c * r * c⁻¹ ∈ P D (!i) := by
      have := hcw r hr
      rw [← v_eq_vt] at this
      exact (smul_v_eq_iff D _ (!i)).1 this
    exact D.rank2.pgen_inter i (hcP r hr) h1
  have hR'mB : R'.map (MulAut.conj (mi D i)).toMonoidHom ≤ D.B := by
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    have h1 : mi D i * (c * r * c⁻¹) * (mi D i)⁻¹ ∈ P D (!i) := by
      have := hcw' r hr
      rw [smul_vt, vt_eq_vt_iff] at this
      have h2 := (P D (!i)).inv_mem this
      simpa [P, mul_assoc] using h2
    have h3 : mi D i * (c * r * c⁻¹) * (mi D i)⁻¹ ∈ P D i :=
      (P D i).mul_mem ((P D i).mul_mem (mi_mem_P D i) (hcP r hr)) ((P D i).inv_mem (mi_mem_P D i))
    exact D.rank2.pgen_inter i h3 h1
  have hR'U := le_U_of_le_B D hU hR'B hR'2
  have hR'mU := le_U_of_le_B D hU hR'mB (hR'2.map _)
  intro r hr
  rw [mem_rad_smul_iff, rad_v, Q_eq_Uplus D hU i]
  have hx : c * r * c⁻¹ ∈ Uplus D i := by
    rw [mem_Uplus_iff]
    exact ⟨hR'U ⟨r, hr, rfl⟩, hR'mU ⟨_, ⟨r, hr, rfl⟩, rfl⟩⟩
  have e : g⁻¹ * r * g = h⁻¹ * (c * r * c⁻¹) * h := by rw [hc]; group
  rw [e]
  have := P_conj_Uplus D ((P D i).inv_mem hh) hx
  simpa using this

theorem exists_sylow_chamber {y u : V D} (h : (Γ D).Adj y u) :
    ∃ S : Subgroup X, IsPGroup 2 S ∧ stab D y ⊓ stab D u ≤ Subgroup.normalizer (S : Set X) ∧
      ∀ R : Subgroup X, R ≤ stab D y ⊓ stab D u → IsPGroup 2 R → R ≤ S := by
  obtain ⟨g, i, rfl⟩ := exists_smul_v D y
  have hu' : (Γ D).Adj (v D i) (g⁻¹ • u) := by
    have := (GraphAction.adj_smul (Γ := Γ D) g⁻¹ (g • v D i) u).2 h
    rwa [inv_smul_smul] at this
  obtain ⟨p, hp, hpu⟩ : ∃ p ∈ P D i, p • v D (!i) = g⁻¹ • u := by
    cases i
    · obtain ⟨p, hp, hpu⟩ := flag_false D _ hu'
      exact ⟨p, hp, hpu⟩
    · obtain ⟨p, hp, hpu⟩ := flag_true D _ hu'
      exact ⟨p, hp, hpu⟩
  set c : X := g * p with hc
  have hy : g • v D i = c • v D i := by rw [hc, mul_smul, (smul_v_eq_iff D p i).2 hp]
  have hu : u = c • v D (!i) := by rw [hc, mul_smul, hpu, smul_inv_smul]
  have hmem : ∀ x, x ∈ stab D (g • v D i) ⊓ stab D u → c⁻¹ * x * c ∈ D.B := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    rw [hy, mem_stab_smul_iff, stab_v] at hx1
    rw [hu, mem_stab_smul_iff, stab_v] at hx2
    exact D.rank2.pgen_inter i hx1 hx2
  refine ⟨D.U.map (MulAut.conj c).toMonoidHom, hU.2.1.map _, ?_, ?_⟩
  · intro x hx
    rw [← Subgroup.map_equiv_normalizer_eq, normalizer_U_eq_B, Subgroup.mem_map_equiv]
    simpa [MulAut.conj_symm_apply] using hmem x hx
  · intro R hR hR2
    have hle : R.map (MulAut.conj c⁻¹).toMonoidHom ≤ D.B := by
      rintro _ ⟨r, hr, rfl⟩
      simpa using hmem r (hR hr)
    have hU' := le_U_of_le_B D hU hle (hR2.map _)
    intro r hr
    rw [Subgroup.mem_map_equiv]
    simpa [MulAut.conj_symm_apply] using hU' ⟨r, hr, rfl⟩

theorem normalizer_stab (y : V D) : Subgroup.normalizer (stab D y : Set X) = stab D y := by
  obtain ⟨g, i, rfl⟩ := exists_smul_v D y
  rw [stab_smul, ← Subgroup.map_equiv_normalizer_eq, stab_v]
  congr 1
  refine le_antisymm ?_ Subgroup.le_normalizer
  calc Subgroup.normalizer (P D i : Set X)
      ≤ Subgroup.normalizer (pCoreOf 2 (P D i) : Set X) := normalizer_le_normalizer_pCoreOf 2 _
    _ = P D i := normalizer_Q D hU i

theorem eq_stab_of_normalizer_sylow {P : Subgroup X} (hP : P ≠ ⊤) (S : Sylow 2 X)
    (hS : Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ P) :
    ∃ c : X, P = D.B.map (MulAut.conj c).toMonoidHom ∨ ∃ i : Bool, P = stab D (c • v D i) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ D.U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  let SU : Sylow 2 X := hU.2.1.toSylow hidx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X SU S
  have hSc : (S : Subgroup X) = D.U.map (MulAut.conj c).toMonoidHom := by
    rw [← hc, Sylow.coe_subgroup_smul]
    rfl
  have hN : Subgroup.normalizer ((S : Subgroup X) : Set X) =
      D.B.map (MulAut.conj c).toMonoidHom := by
    rw [hSc, ← Subgroup.map_equiv_normalizer_eq, normalizer_U_eq_B]
  have hB : D.B ≤ P.map (MulAut.conj c⁻¹).toMonoidHom := by
    intro b hb
    have : c * b * c⁻¹ ∈ P := hS (by rw [hN]; exact ⟨b, hb, rfl⟩)
    exact ⟨c * b * c⁻¹, this, by simp [MulAut.conj_apply]; group⟩
  have hback : ∀ A : Subgroup X, P.map (MulAut.conj c⁻¹).toMonoidHom = A →
      P = A.map (MulAut.conj c).toMonoidHom := by
    intro A hA
    rw [← hA, Subgroup.map_map]
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨c, ?_⟩
  rcases eq_B_or_P_or_top D hB with h1 | ⟨i, h2⟩ | h3
  · exact Or.inl (hback _ h1)
  · refine Or.inr ⟨i, ?_⟩
    rw [hback _ h2, stab_smul, stab_v]
  · exact absurd (by rw [hback _ h3, Subgroup.map_top_of_surjective _ (MulAut.conj c).surjective])
      hP

theorem card_U_true : Nat.card D.U = Nat.card (D.root 1) * Nat.card (Q D true) := by
  have hn := D.three_le
  have hQ := Q_eq_Uplus D hU true
  have hX1U : D.root 1 ≤ D.U := D.root_le_U le_rfl (by omega)
  have hQU : Q D true ≤ D.U := hQ ▸ Uplus_le_U D true
  have hdisj := root_one_inf_Q D hU
  let f : ↥(D.root 1) × ↥(Q D true) → ↥D.U := fun xq =>
    ⟨(xq.1 : X) * xq.2, D.U.mul_mem (hX1U xq.1.2) (hQU xq.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, q⟩ ⟨x', q'⟩ hxq
      have h1 : (x : X) * q = x' * q' := congrArg Subtype.val hxq
      have h2 : (x' : X)⁻¹ * x = q' * (q : X)⁻¹ := by
        calc (x' : X)⁻¹ * x = (x' : X)⁻¹ * (x * q) * (q : X)⁻¹ := by group
          _ = (x' : X)⁻¹ * (x' * q') * (q : X)⁻¹ := by rw [h1]
          _ = q' * (q : X)⁻¹ := by group
      have h3 : (x' : X)⁻¹ * x ∈ D.root 1 ⊓ Q D true :=
        ⟨(D.root 1).mul_mem ((D.root 1).inv_mem x'.2) x.2,
          h2 ▸ (Q D true).mul_mem q'.2 ((Q D true).inv_mem q.2)⟩
      rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at h3
      have hq : (q : X) = q' := by
        rw [← h3] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext hq)
    · rintro ⟨u, hu⟩
      have hu' : u ∈ chainProd D.root (intList 1 n) := D.roots.carrier_eq ▸ hu
      rw [intList_cons (by omega : (1 : ℤ) ≤ n), show (1 : ℤ) + 1 = 2 by norm_num,
        chainProd_cons] at hu'
      obtain ⟨x, hx, w, hw, rfl⟩ := Set.mem_mul.1 hu'
      have hwQ : w ∈ Q D true := by
        rw [hQ, ← SetLike.mem_coe, coe_Uplus_true]
        exact hw
      exact ⟨(⟨x, hx⟩, ⟨w, hwQ⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem card_U_false : Nat.card D.U = Nat.card (D.root n) * Nat.card (Q D false) := by
  have hn := D.three_le
  have hQ := Q_eq_Uplus D hU false
  have hXnU : D.root n ≤ D.U := D.root_le_U (by omega) le_rfl
  have hQU : Q D false ≤ D.U := hQ ▸ Uplus_le_U D false
  have hdisj := root_n_inf_Q D hU
  let f : ↥(D.root n) × ↥(Q D false) → ↥D.U := fun xq =>
    ⟨(xq.2 : X) * xq.1, D.U.mul_mem (hQU xq.2.2) (hXnU xq.1.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, q⟩ ⟨x', q'⟩ hxq
      have h1 : (q : X) * x = q' * x' := congrArg Subtype.val hxq
      have h2 : (x : X) * (x' : X)⁻¹ = (q : X)⁻¹ * q' := by
        calc (x : X) * (x' : X)⁻¹ = (q : X)⁻¹ * (q * x) * (x' : X)⁻¹ := by group
          _ = (q : X)⁻¹ * (q' * x') * (x' : X)⁻¹ := by rw [h1]
          _ = (q : X)⁻¹ * q' := by group
      have h3 : (x : X) * (x' : X)⁻¹ ∈ D.root n ⊓ Q D false :=
        ⟨(D.root n).mul_mem x.2 ((D.root n).inv_mem x'.2),
          h2 ▸ (Q D false).mul_mem ((Q D false).inv_mem q.2) q'.2⟩
      rw [hdisj, Subgroup.mem_bot, mul_inv_eq_one] at h3
      have hq : (q : X) = q' := by
        rw [h3] at h1
        exact mul_right_cancel h1
      exact Prod.ext (Subtype.ext h3) (Subtype.ext hq)
    · rintro ⟨u, hu⟩
      have hu' : u ∈ chainProd D.root (intList 1 n) := D.roots.carrier_eq ▸ hu
      rw [intList_snoc (by omega : (1 : ℤ) ≤ n), chainProd_append, chainProd_singleton] at hu'
      obtain ⟨w, hw, x, hx, rfl⟩ := Set.mem_mul.1 hu'
      have hwQ : w ∈ Q D false := by
        rw [hQ, ← SetLike.mem_coe, coe_Uplus_false]
        exact hw
      exact ⟨(⟨x, hx⟩, ⟨w, hwQ⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem card_Q_ne (h : Nat.card (D.root 1) ≠ Nat.card (D.root n)) :
    Nat.card (Q D true) ≠ Nat.card (Q D false) := by
  intro hQ
  have h1 := card_U_true D hU
  have h2 := card_U_false D hU
  rw [h1, hQ] at h2
  exact h (Nat.eq_of_mul_eq_mul_right Nat.card_pos h2)

theorem map_P_of_map_B (h : Nat.card (D.root 1) ≠ Nat.card (D.root n)) (α : MulAut X)
    (hα : D.B.map α.toMonoidHom = D.B) (i : Bool) : (P D i).map α.toMonoidHom = P D i := by
  have hne := card_Q_ne D hU h
  have hcard : Nat.card ((P D i).map α.toMonoidHom) = Nat.card (P D i) :=
    Subgroup.card_map_of_injective α.injective
  have hBP : D.B ≤ (P D i).map α.toMonoidHom := hα ▸ Subgroup.map_mono (B_le_P D i)
  rcases eq_B_or_P_or_top D hBP with h1 | ⟨j, h2⟩ | h3
  · exfalso
    have hle : P D i ≤ D.B := by
      have := Subgroup.eq_of_le_of_card_ge (B_le_P D i) (by rw [← hcard, h1])
      exact this.symm.le
    exact D.rank2.not_mem_B_of_mem_dc (D.rank2.gen_mem i) (mi_mem_dc D i) (hle (mi_mem_P D i))
  · have hQ : Nat.card (Q D j) = Nat.card (Q D i) := by
      have e1 : pCoreOf 2 ((P D i).map α.toMonoidHom) = (Q D i).map α.toMonoidHom :=
        pCoreOf_map_mulEquiv 2 α (P D i)
      rw [h2] at e1
      change Nat.card (pCoreOf 2 (P D j)) = _
      rw [e1]
      exact Subgroup.card_map_of_injective α.injective
    have hji : j = i := by
      by_contra hji
      cases i <;> cases j
      · exact hji rfl
      · exact hne hQ
      · exact hne hQ.symm
      · exact hji rfl
    rw [h2, hji]
  · exfalso
    have hc : Nat.card (P D i) = Nat.card X := by rw [← hcard, h3, Subgroup.card_top]
    exact P_ne_top D i ((Subgroup.card_eq_iff_eq_top _).1 hc)

theorem map_stab_of_map_borel (h : Nat.card (D.root 1) ≠ Nat.card (D.root n)) (φ : MulAut X)
    (c : X) (hφ : (D.B.map (MulAut.conj c).toMonoidHom).map φ.toMonoidHom =
      D.B.map (MulAut.conj c).toMonoidHom) (i : Bool) :
    (stab D (c • v D i)).map φ.toMonoidHom = stab D (c • v D i) := by
  set ψ : X ≃* X := (MulAut.conj c).trans (φ.trans (MulAut.conj c⁻¹)) with hψ
  have hconj : ∀ H : Subgroup X,
      ((H.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom) = H := by
    intro H
    rw [Subgroup.map_map]
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hmapψ : ∀ H : Subgroup X, H.map ψ.toMonoidHom =
      ((H.map (MulAut.conj c).toMonoidHom).map φ.toMonoidHom).map
        (MulAut.conj c⁻¹).toMonoidHom := by
    intro H
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hψB : D.B.map ψ.toMonoidHom = D.B := by rw [hmapψ, hφ, hconj]
  have hψP := map_P_of_map_B D hU h ψ hψB i
  rw [hmapψ] at hψP
  rw [stab_smul, stab_v]
  have hconj' : ∀ H : Subgroup X,
      ((H.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom) = H := by
    intro H
    rw [Subgroup.map_map]
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have h2 := congrArg (fun H : Subgroup X => H.map (MulAut.conj c).toMonoidHom) hψP
  rwa [hconj'] at h2

theorem exists_vertex_equiv (h : Nat.card (D.root 1) ≠ Nat.card (D.root n)) (α : MulAut X)
    (hα : D.U.map α.toMonoidHom = D.U) :
    ∃ β : V D ≃ V D, (∀ (g : X) (y : V D), β (g • y) = α g • β y) ∧
      (∀ y w : V D, (Γ D).Adj (β y) (β w) ↔ (Γ D).Adj y w) ∧ ∀ i, β (v D i) = v D i := by
  have hαB : D.B.map α.toMonoidHom = D.B := by
    rw [← normalizer_U_eq_B, Subgroup.map_equiv_normalizer_eq, hα]
  have hαP : ∀ i, (P D i).map α.toMonoidHom = P D i := map_P_of_map_B D hU h α hαB
  have hset : ∀ (f : X ≃* X), (∀ i, (P D i).map f.toMonoidHom = P D i) → ∀ i,
      f '' ((pgen D.B D.N D.w₁ D.w₂ i : Subgroup X) : Set X) =
        ((pgen D.B D.N D.w₁ D.w₂ i : Subgroup X) : Set X) := by
    intro f hf i
    have := congrArg (fun H : Subgroup X => (H : Set X)) (hf i)
    simpa [P, Subgroup.coe_map] using this
  have hαP' : ∀ i, (P D i).map α.symm.toMonoidHom = P D i := by
    intro i
    conv_lhs => rw [← hαP i]
    rw [Subgroup.map_map]
    ext x
    simp
  have himg : ∀ (f : X ≃* X), (∀ i, (P D i).map f.toMonoidHom = P D i) → ∀ y : V D,
      f '' (y : Set X) ∈ rankTwoVertices D.B D.N D.w₁ D.w₂ := by
    intro f hf y
    obtain ⟨i, x, rfl⟩ := exists_vtx y
    show f '' (((pgen D.B D.N D.w₁ D.w₂ i : Subgroup X) : Set X) * {x}) ∈ _
    rw [Set.image_mul, Set.image_singleton, hset f hf i]
    exact (vtx D.B D.N D.w₁ D.w₂ i (f x)).2
  let β : V D ≃ V D :=
    { toFun := fun y => ⟨α '' (y : Set X), himg α hαP y⟩
      invFun := fun y => ⟨α.symm '' (y : Set X), himg α.symm hαP' y⟩
      left_inv := fun y => Subtype.ext (by
        show α.symm '' (α '' (y : Set X)) = y
        rw [Set.image_image]
        simp)
      right_inv := fun y => Subtype.ext (by
        show α '' (α.symm '' (y : Set X)) = y
        rw [Set.image_image]
        simp) }
  refine ⟨β, fun g y => ?_, fun y w => ?_, fun i => ?_⟩
  · apply Subtype.ext
    show α '' ((y : Set X) * {g⁻¹}) = ((β y : Set X)) * {(α g)⁻¹}
    rw [Set.image_mul, Set.image_singleton, map_inv]
    rfl
  · show (β y ≠ β w ∧ ((β y : Set X) ∩ (β w : Set X)).Nonempty) ↔
      (y ≠ w ∧ ((y : Set X) ∩ (w : Set X)).Nonempty)
    refine and_congr β.injective.ne_iff ?_
    show (α '' (y : Set X) ∩ α '' (w : Set X)).Nonempty ↔ _
    rw [← Set.image_inter α.injective, Set.image_nonempty]
  · apply Subtype.ext
    rw [v_eq_vt]
    show α '' (((pgen D.B D.N D.w₁ D.w₂ i : Subgroup X) : Set X) * {1}) =
      ((pgen D.B D.N D.w₁ D.w₂ i : Subgroup X) : Set X) * {1}
    rw [Set.image_mul, Set.image_singleton, hset α hαP i, map_one]

theorem exists_adj_ne (y u : V D) : ∃ w, (Γ D).Adj y w ∧ w ≠ u := by
  by_contra hcon
  push Not at hcon
  have h3 := three_le_card_neighborSet D y
  have hsub : (Γ D).neighborSet y ⊆ {u} := fun w hw => hcon w hw
  have h1 : Nat.card ((Γ D).neighborSet y) ≤ 1 := by
    have := Set.ncard_le_ncard hsub (Set.finite_singleton u)
    rw [Set.ncard_singleton] at this
    rwa [← Nat.card_coe_set_eq] at this
  omega

end Finite

end CFSG.Quasithin.RonanE114Low
