module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16Alt
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16SplitFix

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

namespace Q16SplitAux

theorem permBar_add_comm' (a b : permBar 6) : a + b = b + a := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
  rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add, add_comm]

theorem mem_of_card_two {Γ : Type*} [Group Γ] [Finite Γ] {W : Subgroup Γ} (hW : Nat.card W = 2)
    {a : Γ} (ha : a ∈ W) (h1 : a ≠ 1) {y : Γ} (hy : y ∈ W) : y = 1 ∨ y = a := by
  by_contra hcon
  rw [not_or] at hcon
  have hsub : ({1, a, y} : Set Γ) ⊆ W := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact W.one_mem
    · exact ha
    · exact hy
  have h3 : ({1, a, y} : Set Γ).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨1, a, y, h1.symm, fun h => hcon.1 h.symm, fun h => hcon.2 h.symm, rfl⟩
  have h := Set.ncard_le_ncard hsub
  have hW' : (W : Set Γ).ncard = 2 := by rw [← Nat.card_coe_set_eq]; exact hW
  omega

theorem card_le_two_of_forall {Γ : Type*} [Group Γ] [Finite Γ] (W : Subgroup Γ) (a : Γ)
    (h : ∀ y ∈ W, y = 1 ∨ y = a) : Nat.card W ≤ 2 := by
  have hsub : (W : Set Γ) ⊆ {1, a} := fun y hy => by simpa using h y hy
  calc Nat.card W = (W : Set Γ).ncard := Nat.card_coe_set_eq (W : Set Γ)
    _ ≤ ({1, a} : Set Γ).ncard := Set.ncard_le_ncard hsub
    _ ≤ ({a} : Set Γ).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

theorem mem_of_card_four {Γ : Type*} [Group Γ] [Finite Γ] {W : Subgroup Γ} (hW : Nat.card W = 4)
    {a b : Γ} (ha : a ∈ W) (hb : b ∈ W) (haa : a * a = 1) (h1 : a ≠ 1) (h2 : b ≠ 1) (h3 : a ≠ b)
    {y : Γ} (hy : y ∈ W) : y = 1 ∨ y = a ∨ y = b ∨ y = a * b := by
  have hab1 : a * b ≠ 1 := fun h =>
    h3 ((inv_eq_of_mul_eq_one_right haa).symm.trans (inv_eq_of_mul_eq_one_right h))
  have n1 : (1 : Γ) ∉ ({a, b, a * b} : Set Γ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1.symm, h2.symm, hab1.symm⟩
  have n2 : a ∉ ({b, a * b} : Set Γ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h3, fun h => h2 (by simpa using h)⟩
  have n3 : b ≠ a * b := fun h => h1 (by simpa using h)
  have h4 : ({1, a, b, a * b} : Set Γ).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_pair n3]
  have hsub : ({1, a, b, a * b} : Set Γ) ⊆ W := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact W.one_mem
    · exact ha
    · exact hb
    · exact W.mul_mem ha hb
  have hW' : (W : Set Γ).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hW
  have heq := Set.eq_of_subset_of_ncard_le hsub (by omega)
  have hy' : y ∈ ({1, a, b, a * b} : Set Γ) := by rw [heq]; exact hy
  simpa using hy'

theorem t45_mul_self : Q16Split.t45 * Q16Split.t45 = 1 := swap_mul_self 4 5

theorem t45_ne_one : Q16Split.t45 ≠ 1 := by
  unfold Q16Split.t45
  decide

end Q16SplitAux

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (C : Cfg G M X 6)

@[expose] noncomputable def q16S : Subgroup G := (Q16Split.d16.comap C.θ).map M.subtype

theorem mem_q16S {g : G} : g ∈ C.q16S ↔ ∃ h : g ∈ M, C.θ ⟨g, h⟩ ∈ Q16Split.d16 := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨h, hθ⟩
    exact ⟨⟨g, h⟩, hθ, rfl⟩

theorem q16S_le : C.q16S ≤ M := Subgroup.map_subtype_le _

theorem pCoreOf_le_q16S : CFSG.Open.pCoreOf 2 M ≤ C.q16S := fun q hq =>
  C.mem_q16S.2 ⟨pCoreOf_le_self M hq, by
    rw [C.theta_Q (by norm_num) hq]
    exact Subgroup.one_mem _⟩

variable {C}

theorem psi_mem_q16S {ψ : Perm (Fin 6) →* ↥M} (hψ : ∀ σ, C.θ (ψ σ) = σ) {d : Perm (Fin 6)}
    (hd : d ∈ Q16Split.d16) : (ψ d : G) ∈ C.q16S :=
  C.mem_q16S.2 ⟨(ψ d).2, by
    rw [show (⟨(ψ d : G), (ψ d).2⟩ : ↥M) = ψ d from rfl, hψ]
    exact hd⟩

theorem map_theta_q16S {ψ : Perm (Fin 6) →* ↥M} (hψ : ∀ σ, C.θ (ψ σ) = σ) :
    (C.q16S.subgroupOf M).map C.θ = Q16Split.d16 := by
  ext σ
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨_, hθ⟩ := C.mem_q16S.1 (Subgroup.mem_subgroupOf.1 hm)
    exact hθ
  · intro hσ
    exact ⟨ψ σ, Subgroup.mem_subgroupOf.2 (psi_mem_q16S hψ hσ), hψ σ⟩

theorem card_q16S (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    {ψ : Perm (Fin 6) →* ↥M} (hψ : ∀ σ, C.θ (ψ σ) = σ) : Nat.card C.q16S = 256 := by
  have h := C.card_eq_card_inf_mul hR C.q16S_le
  rw [inf_eq_right.2 C.pCoreOf_le_q16S, map_theta_q16S hψ, hQ, Q16Split.card_d16] at h
  omega

theorem isPGroup_q16S (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    {ψ : Perm (Fin 6) →* ↥M} (hψ : ∀ σ, C.θ (ψ σ) = σ) : IsPGroup 2 C.q16S :=
  IsPGroup.of_card (n := 8) (by rw [card_q16S hR hQ hψ]; norm_num)

theorem card_M_sym (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    (hsurj : Function.Surjective C.θ) : Nat.card ↥M = 2 ^ 8 * 45 := by
  rw [Cfg.PiData.q16_card_M (C := C) hR hQ, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
    Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem exists_sylow_q16S (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    (hsurj : Function.Surjective C.θ) {ψ : Perm (Fin 6) →* ↥M} (hψ : ∀ σ, C.θ (ψ σ) = σ) :
    ∃ T : Sylow 2 G, C.q16S ≤ T ∧ (T : Subgroup G) ⊓ M = C.q16S := by
  obtain ⟨T, hT⟩ := (isPGroup_q16S hR hQ hψ).exists_le_sylow
  refine ⟨T, hT, ?_⟩
  have hM := card_M_sym hR hQ hsurj
  have hK2 : IsPGroup 2 ↥((T : Subgroup G) ⊓ M) := T.isPGroup'.to_le inf_le_left
  have hle : Nat.card ↥((T : Subgroup G) ⊓ M) ≤ 2 ^ 8 :=
    Q16Mod.card_le_of_dvd hK2 (n := 2 ^ 8 * 45) (m := 8)
      (by rw [← hM]; exact Subgroup.card_dvd_of_le inf_le_right) (by decide)
  refine (Subgroup.eq_of_le_of_card_ge (le_inf hT C.q16S_le) ?_).symm
  have := card_q16S hR hQ hψ
  omega

end Cfg

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

@[expose] noncomputable def piG (q : G) : permBar 6 :=
  @dite _ (q ∈ CFSG.Open.pCoreOf 2 M) (Classical.propDecidable _)
    (fun h => Multiplicative.toAdd (D.piQ ⟨q, h⟩)) (fun _ => 0)

theorem piG_of_mem {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 M) :
    D.piG q = Multiplicative.toAdd (D.piQ ⟨q, hq⟩) := dif_pos hq

theorem piG_one : D.piG 1 = 0 := by
  rw [D.piG_of_mem (Subgroup.one_mem _)]
  exact congrArg Multiplicative.toAdd (map_one D.piQ)

theorem piG_mul {a b : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) (hb : b ∈ CFSG.Open.pCoreOf 2 M) :
    D.piG (a * b) = D.piG a + D.piG b := by
  rw [D.piG_of_mem ((CFSG.Open.pCoreOf 2 M).mul_mem ha hb), D.piG_of_mem ha, D.piG_of_mem hb]
  exact congrArg Multiplicative.toAdd (map_mul D.piQ ⟨a, ha⟩ ⟨b, hb⟩)

theorem piG_inv {a : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) : D.piG a⁻¹ = D.piG a := by
  have e : (⟨a⁻¹, (CFSG.Open.pCoreOf 2 M).inv_mem ha⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
      (⟨a, ha⟩ : ↥(CFSG.Open.pCoreOf 2 M))⁻¹ := rfl
  rw [D.piG_of_mem ((CFSG.Open.pCoreOf 2 M).inv_mem ha), D.piG_of_mem ha, e, map_inv, toAdd_inv,
    permBar_neg_eq]

theorem piG_conj {m a : G} (hm : m ∈ M) (ha : a ∈ CFSG.Open.pCoreOf 2 M) :
    D.piG (m * a * m⁻¹) = barAct (C.θ ⟨m, hm⟩) (D.piG a) := by
  have hq : m * a * m⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M hm ha
  rw [D.piG_of_mem hq, D.piG_of_mem ha]
  exact D.piQ_conj ⟨m, hm⟩ ⟨a, ha⟩ ⟨m * a * m⁻¹, hq⟩ rfl

theorem piG_injOn (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    {a b : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) (hb : b ∈ CFSG.Open.pCoreOf 2 M)
    (h : D.piG a = D.piG b) : a = b := by
  rw [D.piG_of_mem ha, D.piG_of_mem hb] at h
  exact congrArg Subtype.val (D.q16_piQ_injective hR hQ (Multiplicative.toAdd.injective h))

theorem piG_mem_range (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    {a : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) : D.piG a ∈ Set.range (heartToBar (n := 6)) := by
  rw [D.piG_of_mem ha]
  exact D.q16_piQ_mem_range hR hQ ⟨a, ha⟩

theorem exists_piG_eq {v : permBar 6} (hv : v ∈ Set.range (heartToBar (n := 6))) :
    ∃ a ∈ CFSG.Open.pCoreOf 2 M, D.piG a = v := by
  obtain ⟨u, rfl⟩ := hv
  obtain ⟨q, -, hq⟩ := Subgroup.mem_map.1 (D.heart_mem_piQ_Q u)
  refine ⟨(q : G), q.2, ?_⟩
  rw [D.piG_of_mem q.2]
  exact congrArg Multiplicative.toAdd hq

theorem piG_eq_zero_iff (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    {a : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) : D.piG a = 0 ↔ a = 1 := by
  constructor
  · intro h
    exact D.piG_injOn hR hQ ha (Subgroup.one_mem _) (h.trans D.piG_one.symm)
  · rintro rfl
    exact D.piG_one

end Cfg.PiData

namespace Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (C : Cfg G M X 6)

theorem conj_inv_mem_q16S {t : G} (ht : ∀ s ∈ C.q16S, t * s * t⁻¹ ∈ C.q16S) {s : G}
    (hs : s ∈ C.q16S) : t⁻¹ * s * t ∈ C.q16S := by
  let f : C.q16S → C.q16S := fun x => ⟨t * x * t⁻¹, ht x x.2⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : t * (x : G) * t⁻¹ = t * (y : G) * t⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.1 hinj ⟨s, hs⟩
  have h1 : t * (x : G) * t⁻¹ = s := congrArg Subtype.val hx
  have e : t⁻¹ * s * t = x := by
    rw [← h1]
    group
  rw [e]
  exact x.2

@[expose] def thetaImg (N : Subgroup G) : Subgroup (Perm (Fin 6)) := (N.subgroupOf M).map C.θ

theorem mem_thetaImg {N : Subgroup G} {b : Perm (Fin 6)} :
    b ∈ C.thetaImg N ↔ ∃ m : ↥M, (m : G) ∈ N ∧ C.θ m = b := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.1 hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.2 hm, rfl⟩

structure SplitData where
  D : C.PiData
  hR : Nat.card ↥(Rc X) ≤ 2
  hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16
  ψ : Perm (Fin 6) →* ↥M
  hψ : ∀ σ, C.θ (ψ σ) = σ
  z : G
  hz : z ∈ CFSG.Open.pCoreOf 2 M
  hπz : D.piG z = Q16Alt.zBar

end Cfg

namespace Cfg.SplitData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (P : C.SplitData)

theorem psi_mul (σ τ : Perm (Fin 6)) :
    ((P.ψ (σ * τ) : ↥M) : G) = (P.ψ σ : G) * (P.ψ τ : G) := by
  rw [map_mul]
  rfl

theorem psi_one : ((P.ψ 1 : ↥M) : G) = 1 := by
  rw [map_one]
  rfl

theorem theta_psi (σ : Perm (Fin 6)) : C.θ ⟨(P.ψ σ : G), (P.ψ σ).2⟩ = σ := P.hψ σ

theorem piG_psi_conj {a : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) (σ : Perm (Fin 6)) :
    P.D.piG ((P.ψ σ : G) * a * (P.ψ σ : G)⁻¹) = barAct σ (P.D.piG a) := by
  rw [P.D.piG_conj (P.ψ σ).2 ha, P.theta_psi]

theorem psi_conj_mem {a : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) (σ : Perm (Fin 6)) :
    (P.ψ σ : G) * a * (P.ψ σ : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
  pCoreOf_normalized M (P.ψ σ).2 ha

include P in
theorem mem_Q_of_theta_eq_one {g : G} (hg : g ∈ M) (h : C.θ ⟨g, hg⟩ = 1) :
    g ∈ CFSG.Open.pCoreOf 2 M := by
  have hmem : (⟨g, hg⟩ : ↥M) ∈ C.θ.ker := h
  rw [C.theta_ker_eq P.hR] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

theorem decomp_mem_Q {g : G} (hg : g ∈ M) :
    g * ((P.ψ (C.θ ⟨g, hg⟩) : ↥M) : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  refine P.mem_Q_of_theta_eq_one (M.mul_mem hg (M.inv_mem (P.ψ _).2)) ?_
  show C.θ ((⟨g, hg⟩ : ↥M) * (P.ψ (C.θ ⟨g, hg⟩))⁻¹) = 1
  rw [map_mul, map_inv, P.hψ, mul_inv_cancel]

theorem decomp_eq {m : ↥M} {b : Perm (Fin 6)} (hm : C.θ m = b) :
    ∃ q ∈ CFSG.Open.pCoreOf 2 M, (m : G) = q * (P.ψ b : G) := by
  refine ⟨(m : G) * (P.ψ b : G)⁻¹, ?_, by group⟩
  have := P.decomp_mem_Q m.2
  rwa [show C.θ ⟨(m : G), m.2⟩ = b from hm] at this

theorem decomp {s : G} (hs : s ∈ M) :
    ∃ q ∈ CFSG.Open.pCoreOf 2 M, s = q * (P.ψ (C.θ ⟨s, hs⟩) : G) := by
  obtain ⟨q, hq, h⟩ := P.decomp_eq (m := ⟨s, hs⟩) rfl
  exact ⟨q, hq, h⟩

theorem mul_psi (a a' : G) (c b : Perm (Fin 6)) :
    (a * (P.ψ c : G)) * (a' * (P.ψ b : G)) =
      (a * ((P.ψ c : G) * a' * (P.ψ c : G)⁻¹)) * (P.ψ (c * b) : G) := by
  rw [P.psi_mul]
  group

theorem comm_coord {a a' : G} (ha : a ∈ CFSG.Open.pCoreOf 2 M) (ha' : a' ∈ CFSG.Open.pCoreOf 2 M)
    {c b : Perm (Fin 6)} (hcb : c * b = b * c) :
    (a * (P.ψ c : G)) * (a' * (P.ψ b : G)) = (a' * (P.ψ b : G)) * (a * (P.ψ c : G)) ↔
      P.D.piG a + barAct c (P.D.piG a') = P.D.piG a' + barAct b (P.D.piG a) := by
  rw [P.mul_psi, P.mul_psi, ← hcb, mul_left_inj]
  have h1 : a * ((P.ψ c : G) * a' * (P.ψ c : G)⁻¹) ∈ CFSG.Open.pCoreOf 2 M :=
    (CFSG.Open.pCoreOf 2 M).mul_mem ha (P.psi_conj_mem ha' c)
  have h2 : a' * ((P.ψ b : G) * a * (P.ψ b : G)⁻¹) ∈ CFSG.Open.pCoreOf 2 M :=
    (CFSG.Open.pCoreOf 2 M).mul_mem ha' (P.psi_conj_mem ha b)
  have e : P.D.piG (a * ((P.ψ c : G) * a' * (P.ψ c : G)⁻¹)) =
      P.D.piG a + barAct c (P.D.piG a') := by
    rw [P.D.piG_mul ha (P.psi_conj_mem ha' c), P.piG_psi_conj ha']
  have e' : P.D.piG (a' * ((P.ψ b : G) * a * (P.ψ b : G)⁻¹)) =
      P.D.piG a' + barAct b (P.D.piG a) := by
    rw [P.D.piG_mul ha' (P.psi_conj_mem ha b), P.piG_psi_conj ha]
  constructor
  · intro h
    rw [← e, ← e', h]
  · intro h
    exact P.D.piG_injOn P.hR P.hQ h1 h2 (by rw [e, e']; exact h)

theorem sq_coord {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 M) {b : Perm (Fin 6)} (hb : b * b = 1) :
    (q * (P.ψ b : G)) * (q * (P.ψ b : G)) = 1 ↔ P.D.piG q + barAct b (P.D.piG q) = 0 := by
  rw [P.mul_psi, hb, P.psi_one, mul_one]
  have h1 : q * ((P.ψ b : G) * q * (P.ψ b : G)⁻¹) ∈ CFSG.Open.pCoreOf 2 M :=
    (CFSG.Open.pCoreOf 2 M).mul_mem hq (P.psi_conj_mem hq b)
  rw [← P.D.piG_eq_zero_iff P.hR P.hQ h1, P.D.piG_mul hq (P.psi_conj_mem hq b),
    P.piG_psi_conj hq]

theorem z_ne_one : P.z ≠ 1 := by
  intro h
  have := P.hπz
  rw [h, P.D.piG_one] at this
  exact Q16Alt.zBar_ne_zero this.symm

theorem z_mul_self : P.z * P.z = 1 := P.D.q16_mul_self_eq_one P.hR P.hQ P.hz

theorem z_conj {s : G} (hs : s ∈ C.q16S) : s * P.z * s⁻¹ = P.z := by
  obtain ⟨hsM, hθ⟩ := C.mem_q16S.1 hs
  have hq : s * P.z * s⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M hsM P.hz
  refine P.D.piG_injOn P.hR P.hQ hq P.hz ?_
  rw [P.D.piG_conj hsM P.hz, P.hπz]
  exact Q16Split.barAct_zBar_of_mem_d16 hθ

theorem eq_one_or_z_of_central {y : G} (hy : y ∈ C.q16S)
    (hc : ∀ s ∈ C.q16S, s * y = y * s) : y = 1 ∨ y = P.z := by
  have hyQ : y ∈ CFSG.Open.pCoreOf 2 M := by
    rw [← C.centralizer_Q_eq P.hR]
    exact Subgroup.mem_centralizer_iff.2 fun h hh => hc h (C.pCoreOf_le_q16S hh)
  have hfix : ∀ d ∈ Q16Split.d16, barAct d (P.D.piG y) = P.D.piG y := by
    intro d hd
    have h1 := P.piG_psi_conj hyQ d
    have e : (P.ψ d : G) * y * (P.ψ d : G)⁻¹ = y := by
      rw [hc _ (psi_mem_q16S P.hψ hd)]
      group
    rw [e] at h1
    exact h1.symm
  rcases Q16Split.fix_d16 (P.D.piG_mem_range P.hR P.hQ hyQ) hfix with h0 | hz
  · exact Or.inl ((P.D.piG_eq_zero_iff P.hR P.hQ hyQ).1 h0)
  · exact Or.inr (P.D.piG_injOn P.hR P.hQ hyQ P.hz (hz.trans P.hπz.symm))

@[expose] def z2 : Set G :=
  {x | x ∈ C.q16S ∧ ∀ s ∈ C.q16S, x * s * x⁻¹ * s⁻¹ = 1 ∨ x * s * x⁻¹ * s⁻¹ = P.z}

@[expose] def yA : Set G := {x | x ∈ CFSG.Open.pCoreOf 2 M ∧ P.D.piG x ∈ Q16Split.y4}

theorem piG_comm {x s : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) (hs : s ∈ M) :
    x * s * x⁻¹ * s⁻¹ ∈ CFSG.Open.pCoreOf 2 M ∧
      P.D.piG (x * s * x⁻¹ * s⁻¹) = barAct (C.θ ⟨s, hs⟩) (P.D.piG x) - P.D.piG x := by
  have h1 : x * s * x⁻¹ * s⁻¹ = x * (s * x⁻¹ * s⁻¹) := by group
  have hq : s * x⁻¹ * s⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    pCoreOf_normalized M hs ((CFSG.Open.pCoreOf 2 M).inv_mem hx)
  refine ⟨by rw [h1]; exact (CFSG.Open.pCoreOf 2 M).mul_mem hx hq, ?_⟩
  rw [h1, P.D.piG_mul hx hq, P.D.piG_conj hs ((CFSG.Open.pCoreOf 2 M).inv_mem hx),
    P.D.piG_inv hx, permBar_sub_eq_add, Q16SplitAux.permBar_add_comm']

theorem mem_z2_iff {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) : x ∈ P.z2 ↔ x ∈ P.yA := by
  have hv := P.D.piG_mem_range P.hR P.hQ hx
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hx, (Q16Split.mem_y4_iff hv).2 fun d hd => ?_⟩
    obtain ⟨-, hcπ⟩ := P.piG_comm hx (P.ψ d).2
    rw [P.theta_psi] at hcπ
    rcases h _ (psi_mem_q16S P.hψ hd) with h1 | h1
    · exact Or.inl (by rw [← hcπ, h1, P.D.piG_one])
    · exact Or.inr (by rw [← hcπ, h1, P.hπz])
  · rintro ⟨-, h⟩
    refine ⟨C.pCoreOf_le_q16S hx, fun s hs => ?_⟩
    obtain ⟨hsM, hθ⟩ := C.mem_q16S.1 hs
    obtain ⟨hcQ, hcπ⟩ := P.piG_comm hx hsM
    rcases (Q16Split.mem_y4_iff hv).1 h _ hθ with h1 | h1
    · exact Or.inl ((P.D.piG_eq_zero_iff P.hR P.hQ hcQ).1 (hcπ.trans h1))
    · exact Or.inr (P.D.piG_injOn P.hR P.hQ hcQ P.hz (hcπ.trans (h1.trans P.hπz.symm)))

theorem ncard_yA : P.yA.ncard = 4 := by
  have hinj : Set.InjOn P.D.piG P.yA := fun a ha b hb h =>
    P.D.piG_injOn P.hR P.hQ ha.1 hb.1 h
  have himg : P.D.piG '' P.yA = Q16Split.y4 := by
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha.2
    · intro hv
      obtain ⟨a, haQ, hav⟩ := P.D.exists_piG_eq (Q16Split.y4_subset_range hv)
      exact ⟨a, ⟨haQ, hav ▸ hv⟩, hav⟩
  rw [← hinj.ncard_image, himg, Q16Split.ncard_y4]

structure NBad (N : Subgroup G) : Prop where
  le_S : N ≤ C.q16S
  card : Nat.card N = 16
  comm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x
  sq : ∀ x ∈ N, x * x = 1
  normal : ∀ s ∈ C.q16S, ∀ x ∈ N, s * x * s⁻¹ ∈ N
  cent : ∀ s ∈ C.q16S, (∀ x ∈ N, s * x = x * s) → s ∈ N
  z_mem : P.z ∈ N
  z2_le : {x | x ∈ N ∧ x ∈ P.z2}.ncard ≤ 4
  ne_Q : N ≠ CFSG.Open.pCoreOf 2 M

namespace NBad

variable {P} {N : Subgroup G} (h : P.NBad N)
include h

theorem N_le_M : N ≤ M := h.le_S.trans C.q16S_le

theorem thetaImg_le {b : Perm (Fin 6)} (hb : b ∈ C.thetaImg N) : b ∈ Q16Split.d16 := by
  obtain ⟨m, hmN, rfl⟩ := C.mem_thetaImg.1 hb
  exact (C.mem_q16S.1 (h.le_S hmN)).2

theorem card_mul :
    Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) * Nat.card ↥(C.thetaImg N) = 16 := by
  have := C.card_eq_card_inf_mul P.hR h.N_le_M
  rw [h.card] at this
  exact this.symm

theorem W_normal {s x : G} (hs : s ∈ C.q16S) (hx : x ∈ N ⊓ CFSG.Open.pCoreOf 2 M) :
    s * x * s⁻¹ ∈ N ⊓ CFSG.Open.pCoreOf 2 M :=
  ⟨h.normal s hs x hx.1, pCoreOf_normalized M (C.q16S_le hs) hx.2⟩

theorem card_W_cases :
    Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) = 2 ∨ Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) = 4 ∨
      Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) = 8 := by
  have hmul := h.card_mul
  have hzW : P.z ∈ N ⊓ CFSG.Open.pCoreOf 2 M := ⟨h.z_mem, P.hz⟩
  have hge : 2 ≤ Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) := by
    have hne : N ⊓ CFSG.Open.pCoreOf 2 M ≠ ⊥ := fun hb => P.z_ne_one (by
      have := hb ▸ hzW
      simpa using this)
    exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hlt : Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) < 16 := by
    by_contra hnot
    have hle : Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) ≤ 16 := by
      have := Subgroup.card_le_card_group (N ⊓ CFSG.Open.pCoreOf 2 M)
      calc _ ≤ Nat.card N := Subgroup.card_le_of_le inf_le_left
        _ = 16 := h.card
    have h16 : Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) = 16 := by omega
    apply h.ne_Q
    have e1 : N ⊓ CFSG.Open.pCoreOf 2 M = N :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h16, h.card])
    have e2 : N ⊓ CFSG.Open.pCoreOf 2 M = CFSG.Open.pCoreOf 2 M :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h16, P.hQ])
    rw [← e1, e2]
  generalize Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) = k at hmul hge hlt ⊢
  interval_cases k <;> omega

theorem false_of_card_two (hW : Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) = 2) : False := by
  have hzW : P.z ∈ N ⊓ CFSG.Open.pCoreOf 2 M := ⟨h.z_mem, P.hz⟩
  have hWz : ∀ y ∈ N ⊓ CFSG.Open.pCoreOf 2 M, y = 1 ∨ y = P.z := fun y hy =>
    Q16SplitAux.mem_of_card_two hW hzW P.z_ne_one hy
  have hB : ∀ b ∈ C.thetaImg N, b = 1 ∨ b = Q16Split.t45 := by
    intro b hb
    obtain ⟨m, hmN, rfl⟩ := C.mem_thetaImg.1 hb
    refine Q16Split.eq_one_or_t45 (h.thetaImg_le hb) fun v hv => ?_
    obtain ⟨q, hqQ, rfl⟩ := P.D.exists_piG_eq hv
    obtain ⟨hcQ, hcπ⟩ := P.piG_comm hqQ m.2
    have hcN : q * (m : G) * q⁻¹ * (m : G)⁻¹ ∈ N :=
      N.mul_mem (h.normal q (C.pCoreOf_le_q16S hqQ) m hmN) (N.inv_mem hmN)
    rcases hWz _ ⟨hcN, hcQ⟩ with h1 | h1
    · exact Or.inl (by rw [← hcπ, h1, P.D.piG_one])
    · exact Or.inr (by rw [← hcπ, h1, P.hπz])
  have hle := Q16SplitAux.card_le_two_of_forall _ _ hB
  have := h.card_mul
  rw [hW] at this
  omega

theorem false_of_card_eight (hW : Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) = 8) : False := by
  have hBcard : Nat.card ↥(C.thetaImg N) = 2 := by
    have := h.card_mul
    rw [hW] at this
    omega
  obtain ⟨⟨b, hbB⟩, hb'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    ((Subgroup.one_lt_card_iff_ne_bot _).1 (by omega : 1 < Nat.card ↥(C.thetaImg N)))
  have hb1 : b ≠ 1 := fun h1 => hb' (Subtype.ext h1)
  have hBb : ∀ y ∈ C.thetaImg N, y = 1 ∨ y = b := fun y hy =>
    Q16SplitAux.mem_of_card_two hBcard hbB hb1 hy
  have hbd16 : b ∈ Q16Split.d16 := h.thetaImg_le hbB
  obtain ⟨mb, hmbN, hmb⟩ := C.mem_thetaImg.1 hbB
  have hmb' : C.θ ⟨(mb : G), mb.2⟩ = b := hmb
  have hcentral : ∀ d ∈ Q16Split.d16, d * b = b * d := by
    intro d hd
    have hconj : d * b * d⁻¹ ∈ C.thetaImg N := by
      refine C.mem_thetaImg.2 ⟨P.ψ d * mb * (P.ψ d)⁻¹, ?_, ?_⟩
      · exact h.normal _ (psi_mem_q16S P.hψ hd) _ hmbN
      · rw [map_mul, map_mul, map_inv, P.hψ, hmb]
    rcases hBb _ hconj with h1 | h1
    · exact absurd (by simpa using h1) hb1
    · exact mul_inv_eq_iff_eq_mul.1 h1
  have hWfix : ∀ w ∈ N ⊓ CFSG.Open.pCoreOf 2 M, barAct b (P.D.piG w) = P.D.piG w := by
    intro w hw
    have e : (mb : G) * w * (mb : G)⁻¹ = w := by
      rw [h.comm _ hmbN w (Subgroup.mem_inf.1 hw).1]
      group
    have := P.D.piG_conj mb.2 (Subgroup.mem_inf.1 hw).2
    rw [e, hmb'] at this
    exact this.symm
  have hb45 : b = Q16Split.t45 := by
    by_contra hne
    have h4 := Q16Split.card_fixU_le_four_of_central hbd16 hb1 hne hcentral
    have hinj : Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) ≤ Nat.card ↥(Q16Mod.fixU b) := by
      refine Nat.card_le_card_of_injective (fun w => ⟨P.D.piG (w : G), Q16Mod.mem_fixU.2
        ⟨P.D.piG_mem_range P.hR P.hQ (Subgroup.mem_inf.1 w.2).2, hWfix w w.2⟩⟩) fun w w' hww' => ?_
      exact Subtype.ext (P.D.piG_injOn P.hR P.hQ (Subgroup.mem_inf.1 w.2).2
        (Subgroup.mem_inf.1 w'.2).2 (congrArg Subtype.val hww'))
    omega
  subst hb45
  have hF : (Q16Mod.fixU Q16Split.t45).ncard ≤ 8 := by
    rw [← Nat.card_coe_set_eq]
    exact Q16Split.card_fixU_t45_le
  have hsubF : P.D.piG '' ((N ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) ⊆
      Q16Mod.fixU Q16Split.t45 := by
    rintro _ ⟨w, hw, rfl⟩
    exact Q16Mod.mem_fixU.2
      ⟨P.D.piG_mem_range P.hR P.hQ (Subgroup.mem_inf.1 hw).2, hWfix w hw⟩
  have hinjW : Set.InjOn P.D.piG ((N ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) :=
    fun a ha b hb hab => P.D.piG_injOn P.hR P.hQ (Subgroup.mem_inf.1 ha).2
      (Subgroup.mem_inf.1 hb).2 hab
  have hcardW : ((N ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    exact hW
  have hfixeq : P.D.piG '' ((N ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) =
      Q16Mod.fixU Q16Split.t45 :=
    Set.eq_of_subset_of_ncard_le hsubF (by rw [hinjW.ncard_image, hcardW]; exact hF)
      (Set.toFinite _)
  have hfixmem : ∀ v ∈ Q16Mod.fixU Q16Split.t45, ∃ w ∈ N ⊓ CFSG.Open.pCoreOf 2 M,
      P.D.piG w = v := by
    intro v hv
    rw [← hfixeq] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨w, hw, rfl⟩
  have hA_sub : ∀ x ∈ P.yA, x ∈ N ⊓ CFSG.Open.pCoreOf 2 M := by
    intro x hx
    have hv : P.D.piG x ∈ Q16Mod.fixU Q16Split.t45 :=
      Q16Mod.mem_fixU.2 ⟨Q16Split.y4_subset_range hx.2, Q16Split.barAct_t45_of_mem_y4 hx.2⟩
    obtain ⟨w, hw, hwx⟩ := hfixmem _ hv
    have := P.D.piG_injOn P.hR P.hQ (Subgroup.mem_inf.1 hw).2 hx.1 hwx
    rw [← this]
    exact hw
  have hpsiN : (P.ψ Q16Split.t45 : G) ∈ N := by
    obtain ⟨q₀, hq₀Q, hmbq⟩ := P.decomp_eq hmb
    have hsq : (q₀ * (P.ψ Q16Split.t45 : G)) * (q₀ * (P.ψ Q16Split.t45 : G)) = 1 := by
      rw [← hmbq]
      exact h.sq _ hmbN
    have hfix := (P.sq_coord hq₀Q Q16SplitAux.t45_mul_self).1 hsq
    have hv : P.D.piG q₀ ∈ Q16Mod.fixU Q16Split.t45 := by
      refine Q16Mod.mem_fixU.2 ⟨P.D.piG_mem_range P.hR P.hQ hq₀Q, ?_⟩
      rw [eq_neg_of_add_eq_zero_right hfix, permBar_neg_eq]
    obtain ⟨w, hw, hwq⟩ := hfixmem _ hv
    have hwq' : w = q₀ := P.D.piG_injOn P.hR P.hQ (Subgroup.mem_inf.1 hw).2 hq₀Q hwq
    have hq₀N : q₀ ∈ N := hwq' ▸ (Subgroup.mem_inf.1 hw).1
    have e : (P.ψ Q16Split.t45 : G) = q₀⁻¹ * (mb : G) := by
      rw [hmbq]
      group
    rw [e]
    exact N.mul_mem (N.inv_mem hq₀N) hmbN
  have hpsiZ2 : (P.ψ Q16Split.t45 : G) ∈ P.z2 := by
    refine ⟨psi_mem_q16S P.hψ Q16Split.t45_mem_d16, fun s hs => ?_⟩
    obtain ⟨hsM, hθs⟩ := C.mem_q16S.1 hs
    obtain ⟨q, hqQ, hsq⟩ := P.decomp hsM
    have hcomm : Commute (P.ψ Q16Split.t45 : G) (P.ψ (C.θ ⟨s, hsM⟩) : G) := by
      show (P.ψ Q16Split.t45 : G) * (P.ψ (C.θ ⟨s, hsM⟩) : G) =
        (P.ψ (C.θ ⟨s, hsM⟩) : G) * (P.ψ Q16Split.t45 : G)
      rw [← P.psi_mul, ← P.psi_mul, ← Q16Split.t45_comm hθs]
    generalize (P.ψ (C.θ ⟨s, hsM⟩) : G) = ε at hsq hcomm
    have hc' : ε * (P.ψ Q16Split.t45 : G)⁻¹ * ε⁻¹ = (P.ψ Q16Split.t45 : G)⁻¹ := by
      rw [← hcomm.inv_left.eq, mul_inv_cancel_right]
    have e : (P.ψ Q16Split.t45 : G) * s * (P.ψ Q16Split.t45 : G)⁻¹ * s⁻¹ =
        (P.ψ Q16Split.t45 : G) * q * (P.ψ Q16Split.t45 : G)⁻¹ * q⁻¹ := by
      rw [hsq]
      calc (P.ψ Q16Split.t45 : G) * (q * ε) * (P.ψ Q16Split.t45 : G)⁻¹ * (q * ε)⁻¹
          = (P.ψ Q16Split.t45 : G) * q * (ε * (P.ψ Q16Split.t45 : G)⁻¹ * ε⁻¹) * q⁻¹ := by group
        _ = _ := by rw [hc']
    have hq1 : (P.ψ Q16Split.t45 : G) * q * (P.ψ Q16Split.t45 : G)⁻¹ ∈
        CFSG.Open.pCoreOf 2 M := P.psi_conj_mem hqQ _
    have hq2 : (P.ψ Q16Split.t45 : G) * q * (P.ψ Q16Split.t45 : G)⁻¹ * q⁻¹ ∈
        CFSG.Open.pCoreOf 2 M :=
      (CFSG.Open.pCoreOf 2 M).mul_mem hq1 ((CFSG.Open.pCoreOf 2 M).inv_mem hqQ)
    have hpi : P.D.piG ((P.ψ Q16Split.t45 : G) * q * (P.ψ Q16Split.t45 : G)⁻¹ * q⁻¹) =
        barAct Q16Split.t45 (P.D.piG q) - P.D.piG q := by
      rw [P.D.piG_mul hq1 ((CFSG.Open.pCoreOf 2 M).inv_mem hqQ), P.piG_psi_conj hqQ,
        P.D.piG_inv hqQ, permBar_sub_eq_add]
    rw [e]
    rcases Q16Split.barAct_t45_sub (P.D.piG_mem_range P.hR P.hQ hqQ) with h0 | hz
    · exact Or.inl ((P.D.piG_eq_zero_iff P.hR P.hQ hq2).1 (hpi.trans h0))
    · exact Or.inr (P.D.piG_injOn P.hR P.hQ hq2 P.hz (hpi.trans (hz.trans P.hπz.symm)))
  have hnot : (P.ψ Q16Split.t45 : G) ∉ P.yA := by
    intro hmem
    have h1 := C.theta_Q (by norm_num) hmem.1
    rw [P.theta_psi] at h1
    exact Q16SplitAux.t45_ne_one h1
  have hsub5 : insert (P.ψ Q16Split.t45 : G) P.yA ⊆ {x | x ∈ N ∧ x ∈ P.z2} := by
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨hpsiN, hpsiZ2⟩
    · exact ⟨(Subgroup.mem_inf.1 (hA_sub x hx)).1, (P.mem_z2_iff hx.1).2 hx⟩
  have h5 : (insert (P.ψ Q16Split.t45 : G) P.yA).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem hnot, P.ncard_yA]
  have h6 := Set.ncard_le_ncard hsub5
  have h7 := h.z2_le
  omega

theorem false_of_card_four (hW : Nat.card ↥(N ⊓ CFSG.Open.pCoreOf 2 M) = 4) : False := by
  have hBcard : Nat.card ↥(C.thetaImg N) = 4 := by
    have := h.card_mul
    rw [hW] at this
    omega
  have hzW : P.z ∈ N ⊓ CFSG.Open.pCoreOf 2 M := ⟨h.z_mem, P.hz⟩
  have hWyA : ∀ x ∈ N ⊓ CFSG.Open.pCoreOf 2 M, x ∈ P.yA := by
    intro x hx
    refine (P.mem_z2_iff (Subgroup.mem_inf.1 hx).2).1
      ⟨h.le_S (Subgroup.mem_inf.1 hx).1, fun s hs => ?_⟩
    by_cases hx1 : x = 1
    · exact Or.inl (by rw [hx1]; group)
    by_cases hxz : x = P.z
    · refine Or.inl ?_
      have hinv : s * P.z⁻¹ * s⁻¹ = P.z⁻¹ := by
        rw [show s * P.z⁻¹ * s⁻¹ = (s * P.z * s⁻¹)⁻¹ by group, P.z_conj hs]
      rw [hxz]
      calc P.z * s * P.z⁻¹ * s⁻¹ = P.z * (s * P.z⁻¹ * s⁻¹) := by group
        _ = 1 := by rw [hinv, mul_inv_cancel]
    have hy := h.W_normal hs hx
    have hy1 : s * x * s⁻¹ ≠ 1 := fun h1 => hx1 (by simpa using h1)
    have hyz : s * x * s⁻¹ ≠ P.z := by
      intro h1
      apply hxz
      have h2 : s * x * s⁻¹ = s * P.z * s⁻¹ := by rw [h1, P.z_conj hs]
      exact mul_left_cancel (mul_right_cancel h2)
    have hcases := Q16SplitAux.mem_of_card_four hW hzW hx P.z_mul_self P.z_ne_one hx1
      (fun h1 => hxz h1.symm) hy
    have e : x * s * x⁻¹ * s⁻¹ = x * (s * x * s⁻¹)⁻¹ := by group
    rw [e]
    rcases hcases with h1 | h1 | h1 | h1
    · exact absurd h1 hy1
    · exact absurd h1 hyz
    · exact Or.inl (by rw [h1, mul_inv_cancel])
    · refine Or.inr ?_
      rw [h1, mul_inv_rev, mul_inv_cancel_left, inv_eq_of_mul_eq_one_right P.z_mul_self]
  have hAeq : ((N ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) = P.yA := by
    refine Set.eq_of_subset_of_ncard_le (fun x hx => hWyA x hx) ?_ (Set.toFinite _)
    have : ((N ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hW
    rw [P.ncard_yA]
    omega
  have hy4W : ∀ v ∈ Q16Split.y4, ∃ w ∈ N ⊓ CFSG.Open.pCoreOf 2 M, P.D.piG w = v := by
    intro v hv
    obtain ⟨a, haQ, hav⟩ := P.D.exists_piG_eq (Q16Split.y4_subset_range hv)
    have haA : a ∈ P.yA := ⟨haQ, hav ▸ hv⟩
    rw [← hAeq] at haA
    exact ⟨a, haA, hav⟩
  have hBb8 : ∀ b ∈ C.thetaImg N, b ∈ Q16Split.b8 := by
    intro b hb
    obtain ⟨m, hmN, rfl⟩ := C.mem_thetaImg.1 hb
    refine Q16Split.mem_b8_of_fix_y4 (h.thetaImg_le hb) fun v hv => ?_
    obtain ⟨w, hw, rfl⟩ := hy4W v hv
    have e : (m : G) * w * (m : G)⁻¹ = w := by
      rw [h.comm _ hmN w (Subgroup.mem_inf.1 hw).1]
      group
    have := P.D.piG_conj m.2 (Subgroup.mem_inf.1 hw).2
    rw [e] at this
    exact this.symm
  obtain ⟨⟨b₁, hb₁B⟩, hb₁'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    ((Subgroup.one_lt_card_iff_ne_bot _).1 (by omega : 1 < Nat.card ↥(C.thetaImg N)))
  have hb₁1 : b₁ ≠ 1 := fun h1 => hb₁' (Subtype.ext h1)
  obtain ⟨b₂, hb₂B, hb₂1, hb₂₁⟩ : ∃ b₂ ∈ C.thetaImg N, b₂ ≠ 1 ∧ b₂ ≠ b₁ := by
    by_contra hcon
    have := Q16SplitAux.card_le_two_of_forall (C.thetaImg N) b₁ (fun y hy => by
      by_cases hy1 : y = 1
      · exact Or.inl hy1
      · exact Or.inr (by
          by_contra hy2
          exact hcon ⟨y, hy, hy1, hy2⟩))
    omega
  obtain ⟨m₁, hm₁N, hm₁⟩ := C.mem_thetaImg.1 hb₁B
  obtain ⟨m₂, hm₂N, hm₂⟩ := C.mem_thetaImg.1 hb₂B
  have hb₁sq : b₁ * b₁ = 1 := by
    have h1 : (m₁ * m₁ : ↥M) = 1 := Subtype.ext (h.sq _ hm₁N)
    rw [← hm₁, ← map_mul, h1, map_one]
  have hb₂sq : b₂ * b₂ = 1 := by
    have h1 : (m₂ * m₂ : ↥M) = 1 := Subtype.ext (h.sq _ hm₂N)
    rw [← hm₂, ← map_mul, h1, map_one]
  have hBcases : ∀ y ∈ C.thetaImg N, y = 1 ∨ y = b₁ ∨ y = b₂ ∨ y = b₁ * b₂ := fun y hy =>
    Q16SplitAux.mem_of_card_four hBcard hb₁B hb₂B hb₁sq hb₁1 hb₂1 (Ne.symm hb₂₁) hy
  obtain ⟨q₁, hq₁Q, hq₁⟩ := P.decomp_eq hm₁
  obtain ⟨q₂, hq₂Q, hq₂⟩ := P.decomp_eq hm₂
  have hb₁8 := hBb8 _ hb₁B
  have hb₂8 := hBb8 _ hb₂B
  have hcomm12 : b₁ * b₂ = b₂ * b₁ := Q16Split.b8_comm hb₁8 hb₂8
  have e₁ : barAct b₁ (P.D.piG q₁) = P.D.piG q₁ := by
    have := (P.sq_coord hq₁Q hb₁sq).1 (by rw [← hq₁]; exact h.sq _ hm₁N)
    rw [eq_neg_of_add_eq_zero_right this, permBar_neg_eq]
  have e₂ : barAct b₂ (P.D.piG q₂) = P.D.piG q₂ := by
    have := (P.sq_coord hq₂Q hb₂sq).1 (by rw [← hq₂]; exact h.sq _ hm₂N)
    rw [eq_neg_of_add_eq_zero_right this, permBar_neg_eq]
  have e : P.D.piG q₁ + barAct b₁ (P.D.piG q₂) = P.D.piG q₂ + barAct b₂ (P.D.piG q₁) := by
    refine (P.comm_coord hq₁Q hq₂Q hcomm12).1 ?_
    rw [← hq₁, ← hq₂]
    exact h.comm _ hm₁N _ hm₂N
  obtain ⟨c, hc8, hc1, hcb₁, hcb₂, hcb₁₂, u, hu, hu₁, hu₂⟩ :=
    Q16Split.exists_centralizing hb₁8 hb₂8 hb₁1 hb₂1 (Ne.symm hb₂₁)
      (P.D.piG_mem_range P.hR P.hQ hq₁Q) (P.D.piG_mem_range P.hR P.hQ hq₂Q) e₁ e₂ e
  obtain ⟨a, haQ, hau⟩ := P.D.exists_piG_eq hu
  have hcd16 : c ∈ Q16Split.d16 := Q16Split.b8_le_d16 hc8
  have hxS : a * (P.ψ c : G) ∈ C.q16S :=
    C.q16S.mul_mem (C.pCoreOf_le_q16S haQ) (psi_mem_q16S P.hψ hcd16)
  have hx₁ : (a * (P.ψ c : G)) * (m₁ : G) = (m₁ : G) * (a * (P.ψ c : G)) := by
    rw [hq₁]
    exact (P.comm_coord haQ hq₁Q (Q16Split.b8_comm hc8 hb₁8)).2 (by rw [hau]; exact hu₁)
  have hx₂ : (a * (P.ψ c : G)) * (m₂ : G) = (m₂ : G) * (a * (P.ψ c : G)) := by
    rw [hq₂]
    exact (P.comm_coord haQ hq₂Q (Q16Split.b8_comm hc8 hb₂8)).2 (by rw [hau]; exact hu₂)
  have hxW : ∀ w ∈ N ⊓ CFSG.Open.pCoreOf 2 M,
      (a * (P.ψ c : G)) * w = w * (a * (P.ψ c : G)) := by
    intro w hw
    have hwQ := (Subgroup.mem_inf.1 hw).2
    have hψw : (P.ψ c : G) * w * (P.ψ c : G)⁻¹ = w := by
      refine P.D.piG_injOn P.hR P.hQ (P.psi_conj_mem hwQ c) hwQ ?_
      rw [P.piG_psi_conj hwQ]
      exact Q16Split.barAct_of_mem_b8_of_mem_y4 hc8 (hWyA w hw).2
    have hψw' : (P.ψ c : G) * w = w * (P.ψ c : G) := mul_inv_eq_iff_eq_mul.1 hψw
    calc a * (P.ψ c : G) * w = a * ((P.ψ c : G) * w) := by group
      _ = a * (w * (P.ψ c : G)) := by rw [hψw']
      _ = (a * w) * (P.ψ c : G) := by group
      _ = (w * a) * (P.ψ c : G) := by rw [C.Q_comm P.hR a haQ w hwQ]
      _ = w * (a * (P.ψ c : G)) := by group
  have hxN : ∀ n ∈ N, (a * (P.ψ c : G)) * n = n * (a * (P.ψ c : G)) := by
    intro n hn
    have hnM : n ∈ M := h.N_le_M hn
    have hnB : C.θ ⟨n, hnM⟩ ∈ C.thetaImg N := C.mem_thetaImg.2 ⟨⟨n, hnM⟩, hn, rfl⟩
    obtain ⟨r, hrN, hrx, hrM, hrθ⟩ : ∃ r ∈ N, (a * (P.ψ c : G)) * r = r * (a * (P.ψ c : G)) ∧
        ∃ hrM : r ∈ M, C.θ ⟨r, hrM⟩ = C.θ ⟨n, hnM⟩ := by
      rcases hBcases _ hnB with h1 | h1 | h1 | h1
      · exact ⟨1, N.one_mem, by group, M.one_mem, by rw [h1]; exact map_one C.θ⟩
      · exact ⟨m₁, hm₁N, hx₁, m₁.2, by rw [h1]; exact hm₁⟩
      · exact ⟨m₂, hm₂N, hx₂, m₂.2, by rw [h1]; exact hm₂⟩
      · refine ⟨(m₁ : G) * m₂, N.mul_mem hm₁N hm₂N, ?_, M.mul_mem m₁.2 m₂.2, ?_⟩
        · calc (a * (P.ψ c : G)) * ((m₁ : G) * m₂)
              = ((a * (P.ψ c : G)) * m₁) * m₂ := by group
            _ = (m₁ * (a * (P.ψ c : G))) * m₂ := by rw [hx₁]
            _ = m₁ * ((a * (P.ψ c : G)) * m₂) := by group
            _ = m₁ * (m₂ * (a * (P.ψ c : G))) := by rw [hx₂]
            _ = ((m₁ : G) * m₂) * (a * (P.ψ c : G)) := by group
        · rw [h1]
          exact (by rw [show (⟨(m₁ : G) * m₂, M.mul_mem m₁.2 m₂.2⟩ : ↥M) = m₁ * m₂ from rfl,
            map_mul, hm₁, hm₂])
    have hwN : n * r⁻¹ ∈ N := N.mul_mem hn (N.inv_mem hrN)
    have hwM : n * r⁻¹ ∈ M := M.mul_mem hnM (M.inv_mem hrM)
    have hwθ : C.θ ⟨n * r⁻¹, hwM⟩ = 1 := by
      show C.θ ((⟨n, hnM⟩ : ↥M) * (⟨r, hrM⟩ : ↥M)⁻¹) = 1
      rw [map_mul, map_inv, hrθ, mul_inv_cancel]
    have hwQ : n * r⁻¹ ∈ CFSG.Open.pCoreOf 2 M := P.mem_Q_of_theta_eq_one hwM hwθ
    have hxw := hxW _ ⟨hwN, hwQ⟩
    calc (a * (P.ψ c : G)) * n = (a * (P.ψ c : G)) * ((n * r⁻¹) * r) := by group
      _ = ((a * (P.ψ c : G)) * (n * r⁻¹)) * r := by group
      _ = ((n * r⁻¹) * (a * (P.ψ c : G))) * r := by rw [hxw]
      _ = (n * r⁻¹) * ((a * (P.ψ c : G)) * r) := by group
      _ = (n * r⁻¹) * (r * (a * (P.ψ c : G))) := by rw [hrx]
      _ = n * (a * (P.ψ c : G)) := by group
  have hxN' : a * (P.ψ c : G) ∈ N := h.cent _ hxS hxN
  have hcB : c ∈ C.thetaImg N := by
    refine C.mem_thetaImg.2 ⟨(⟨a, pCoreOf_le_self M haQ⟩ : ↥M) * P.ψ c, hxN', ?_⟩
    rw [map_mul, P.hψ, C.theta_Q (by norm_num) haQ, one_mul]
  rcases hBcases c hcB with h1 | h1 | h1 | h1
  · exact hc1 h1
  · exact hcb₁ h1
  · exact hcb₂ h1
  · exact hcb₁₂ h1

theorem contradiction : False := by
  rcases h.card_W_cases with h2 | h4 | h8
  · exact h.false_of_card_two h2
  · exact h.false_of_card_four h4
  · exact h.false_of_card_eight h8

end NBad

theorem exists_nbad {t : G} (ht : ∀ s ∈ C.q16S, t * s * t⁻¹ ∈ C.q16S) (htM : t ∉ M) :
    ∃ N : Subgroup G, P.NBad N := by
  have hinv : ∀ s ∈ C.q16S, t⁻¹ * s * t ∈ C.q16S := fun s hs => C.conj_inv_mem_q16S ht hs
  have htz : t * P.z * t⁻¹ = P.z := by
    have hS : t * P.z * t⁻¹ ∈ C.q16S := ht _ (C.pCoreOf_le_q16S P.hz)
    refine (P.eq_one_or_z_of_central hS fun s hs => ?_).resolve_left fun h1 =>
      P.z_ne_one (by simpa using h1)
    have hc : (t⁻¹ * s * t) * P.z = P.z * (t⁻¹ * s * t) :=
      mul_inv_eq_iff_eq_mul.1 (P.z_conj (hinv s hs))
    calc s * (t * P.z * t⁻¹) = t * ((t⁻¹ * s * t) * P.z) * t⁻¹ := by group
      _ = t * (P.z * (t⁻¹ * s * t)) * t⁻¹ := by rw [hc]
      _ = (t * P.z * t⁻¹) * s := by group
  have htz' : t⁻¹ * P.z * t = P.z :=
    calc t⁻¹ * P.z * t = t⁻¹ * (t * P.z * t⁻¹) * t := by rw [htz]
      _ = P.z := by group
  refine ⟨CFSG.CGT.Timmesfeld75.conjSubgroup t (CFSG.Open.pCoreOf 2 M), ?_⟩
  have hmem : ∀ {x : G}, x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup t (CFSG.Open.pCoreOf 2 M) ↔
      t⁻¹ * x * t ∈ CFSG.Open.pCoreOf 2 M := CFSG.CGT.Timmesfeld75.mem_conjSubgroup
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    have hxQ := hmem.1 hx
    have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [e]
    exact ht _ (C.pCoreOf_le_q16S hxQ)
  ·
    show Nat.card ↥((CFSG.Open.pCoreOf 2 M).map (MulAut.conj t).toMonoidHom) = 16
    rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, P.hQ]
  ·
    intro x hx y hy
    have h1 := C.Q_comm P.hR _ (hmem.1 hx) _ (hmem.1 hy)
    calc x * y = t * ((t⁻¹ * x * t) * (t⁻¹ * y * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * y * t) * (t⁻¹ * x * t)) * t⁻¹ := by rw [h1]
      _ = y * x := by group
  ·
    intro x hx
    have h1 := P.D.q16_mul_self_eq_one P.hR P.hQ (hmem.1 hx)
    calc x * x = t * ((t⁻¹ * x * t) * (t⁻¹ * x * t)) * t⁻¹ := by group
      _ = 1 := by rw [h1]; group
  ·
    intro s hs x hx
    refine hmem.2 ?_
    have e : t⁻¹ * (s * x * s⁻¹) * t = (t⁻¹ * s * t) * (t⁻¹ * x * t) * (t⁻¹ * s * t)⁻¹ := by group
    rw [e]
    exact pCoreOf_normalized M (C.q16S_le (hinv s hs)) (hmem.1 hx)
  ·
    intro s hs hc
    refine hmem.2 ?_
    rw [← C.centralizer_Q_eq P.hR]
    refine Subgroup.mem_centralizer_iff.2 fun q hq => ?_
    have hxN : t * q * t⁻¹ ∈ CFSG.CGT.Timmesfeld75.conjSubgroup t (CFSG.Open.pCoreOf 2 M) := by
      refine hmem.2 ?_
      have e : t⁻¹ * (t * q * t⁻¹) * t = q := by group
      rw [e]
      exact hq
    have h1 := hc _ hxN
    calc q * (t⁻¹ * s * t) = t⁻¹ * ((t * q * t⁻¹) * s) * t := by group
      _ = t⁻¹ * (s * (t * q * t⁻¹)) * t := by rw [h1]
      _ = (t⁻¹ * s * t) * q := by group
  ·
    refine hmem.2 ?_
    rw [htz']
    exact P.hz
  ·
    have hmaps : ∀ x ∈ {x | x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup t (CFSG.Open.pCoreOf 2 M) ∧
        x ∈ P.z2}, (fun x => t⁻¹ * x * t) x ∈ P.yA := by
      rintro x ⟨hxN, hxS, hxz⟩
      have hxQ : t⁻¹ * x * t ∈ CFSG.Open.pCoreOf 2 M := hmem.1 hxN
      refine (P.mem_z2_iff hxQ).1 ⟨hinv x hxS, fun s hs => ?_⟩
      have e : t⁻¹ * x * t * s * (t⁻¹ * x * t)⁻¹ * s⁻¹ =
          t⁻¹ * (x * (t * s * t⁻¹) * x⁻¹ * (t * s * t⁻¹)⁻¹) * t := by group
      rw [e]
      rcases hxz _ (ht s hs) with h1 | h1
      · exact Or.inl (by rw [h1]; group)
      · exact Or.inr (by rw [h1, htz'])
    calc _ ≤ P.yA.ncard := Set.ncard_le_ncard_of_injOn (fun x => t⁻¹ * x * t) hmaps
          (fun x _ y _ hxy => mul_left_cancel (mul_right_cancel hxy)) (Set.toFinite _)
      _ = 4 := P.ncard_yA
  ·
    intro hNQ
    apply htM
    have key : ∀ x : G, t⁻¹ * x * t ∈ CFSG.Open.pCoreOf 2 M ↔ x ∈ CFSG.Open.pCoreOf 2 M := by
      intro x
      rw [← hmem, hNQ]
    have hnorm : t ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro q
      have e : t⁻¹ * (t * q * t⁻¹) * t = q := by group
      have := key (t * q * t⁻¹)
      rw [e] at this
      exact this
    rwa [C.S.normalizer_Q_eq] at hnorm

end Cfg.SplitData

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

include D in
theorem q16_mem_M_of_normalizes_split (hR : Nat.card ↥(Rc X) ≤ 2)
    (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16) {ψ : Perm (Fin 6) →* ↥M} (hψ : ∀ σ, C.θ (ψ σ) = σ) {t : G}
    (ht : ∀ s ∈ C.q16S, t * s * t⁻¹ ∈ C.q16S) : t ∈ M := by
  obtain ⟨z, hz, hπz⟩ := D.exists_q16_z
  let P : C.SplitData := ⟨D, hR, hQ, ψ, hψ, z, hz, by rw [D.piG_of_mem hz]; exact hπz⟩
  by_contra htM
  obtain ⟨N, hN⟩ := P.exists_nbad ht htM
  exact hN.contradiction

include D in
theorem q16_false_split (hR : Nat.card ↥(Rc X) ≤ 2) (hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16)
    (hsurj : Function.Surjective C.θ)
    (hsplit : ∃ ψ : Perm (Fin 6) →* ↥M, ∀ σ, C.θ (ψ σ) = σ) : False := by
  obtain ⟨ψ, hψ⟩ := hsplit
  obtain ⟨T, hST, hTM⟩ := C.exists_sylow_q16S hR hQ hsurj hψ
  by_cases hTS : (T : Subgroup G) ≤ C.q16S
  · exact D.q16_false_of_sylow_le hR hQ T (hTS.trans C.q16S_le)
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥(T : Subgroup G) := T.isPGroup'.isNilpotent
    have hlt : C.q16S.subgroupOf (T : Subgroup G) < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => hTS fun x hx => ?_
      have : (⟨x, hx⟩ : ↥(T : Subgroup G)) ∈ C.q16S.subgroupOf (T : Subgroup G) := by
        rw [htop]
        trivial
      exact Subgroup.mem_subgroupOf.1 this
    obtain ⟨x, hxN, hxS⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hnorm : ∀ s ∈ C.q16S, (x : G) * s * (x : G)⁻¹ ∈ C.q16S := by
      intro s hs
      have := (Subgroup.mem_normalizer_iff.1 hxN ⟨s, hST hs⟩).1 (Subgroup.mem_subgroupOf.2 hs)
      exact Subgroup.mem_subgroupOf.1 this
    have hxM := D.q16_mem_M_of_normalizes_split hR hQ hψ hnorm
    apply hxS
    rw [Subgroup.mem_subgroupOf, ← hTM]
    exact Subgroup.mem_inf.2 ⟨x.2, hxM⟩

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
