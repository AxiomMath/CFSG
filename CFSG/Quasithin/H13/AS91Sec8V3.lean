module

public import CFSG.Quasithin.H13.AS91Sec8HGeom
public import CFSG.Quasithin.H13.AS91Sec8Defs

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem smul_x0_eq_iff_of_autPres {φ : ↥c.G3 ≃* ↥c.G3}
    (hφ : autPres c.G3 (c.G3 ⊓ stabilizer G c.x0) φ) (d : ↥c.G3) :
    ((φ d : ↥c.G3) : G) • c.x0 = c.x0 ↔ (d : G) • c.x0 = c.x0 := by
  rw [← MulAction.mem_stabilizer_iff, ← MulAction.mem_stabilizer_iff]
  have h := hφ d
  rw [Subgroup.mem_inf, Subgroup.mem_inf] at h
  simpa [d.2, (φ d).2] using h.symm

theorem exists_swap (hG2 : Stmt5_Gamma2) {G : Type} [Group G] [Finite G] {z : G}
    (hJ : HypJ4 G z) (c : Loc49 G z) {y : G ⧸ c.G1} (hy : y ∈ c.nbrP) :
    ∃ σ ∈ c.G3, σ • c.x0 = y ∧ σ • y = c.x0 := by
  classical
  have hyOrb : y ∈ MulAction.orbit ↥c.G3 c.x0 := by
    rw [← c.ptsP_eq_orbit]
    exact hy.1
  obtain ⟨g, hg⟩ := hyOrb
  let h : ↥c.G3 := g⁻¹
  have hhy : ((h : ↥c.G3) : G) • y = c.x0 := by
    rw [← hg]
    change ((g⁻¹ : ↥c.G3) : G) • ((g : ↥c.G3) • c.x0) = c.x0
    rw [Subgroup.smul_def, ← mul_smul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      one_smul]
  have hhP : ((h : ↥c.G3) : G) • c.x0 ∈ c.ptsP := by
    have hfix : ((h : ↥c.G3) : G) • c.pi0 = c.pi0 := c.G3_smul_pi0 h.2
    have h := (c.onP_smul_iff ((h : ↥c.G3) : G)).mpr c.x0_mem_ptsP
    rwa [hfix] at h
  have hhAdj : c.Delta.Adj (((h : ↥c.G3) : G) • c.x0) c.x0 := by
    have h := (c.adj_smul_iff ((h : ↥c.G3) : G)).2 hy.2
    rwa [hhy] at h
  have hhN : ((h : ↥c.G3) : G) • c.x0 ∈ c.nbrP := ⟨hhP, hhAdj.symm⟩
  have horb : MulAction.orbit ↥(c.G1.subgroupOf c.G3) y = c.nbrP :=
    c.orbit_subgroupOf_G1_eq_nbrP hG2 hJ hy
  have hmem : ((h : ↥c.G3) : G) • c.x0 ∈
      MulAction.orbit ↥(c.G1.subgroupOf c.G3) y := by
    rw [horb]
    exact hhN
  obtain ⟨i, hi⟩ := hmem
  have hi_smul : ((i : ↥c.G3) : G) • y = ((h : ↥c.G3) : G) • c.x0 := by
    simpa only [Subgroup.smul_def] using hi
  have hiG1 : ((i : ↥c.G3) : G) ∈ c.G1 := Subgroup.mem_subgroupOf.mp i.2
  have hix : ((i : ↥c.G3) : G) • c.x0 = c.x0 := c.smul_x0_of_mem hiG1
  have hix_inv : ((i : ↥c.G3) : G)⁻¹ • c.x0 = c.x0 := by
    calc ((i : ↥c.G3) : G)⁻¹ • c.x0
        = ((i : ↥c.G3) : G)⁻¹ • (((i : ↥c.G3) : G) • c.x0) := by rw [hix]
      _ = c.x0 := inv_smul_smul _ _
  let σ : ↥c.G3 := (i : ↥c.G3)⁻¹ * h
  refine ⟨σ, σ.2, ?_, ?_⟩
  · change (((i : ↥c.G3) : G)⁻¹ * ((h : ↥c.G3) : G)) • c.x0 = y
    rw [mul_smul, ← hi_smul, inv_smul_smul]
  · change (((i : ↥c.G3) : G)⁻¹ * ((h : ↥c.G3) : G)) • y = c.x0
    rw [mul_smul, hhy, hix_inv]

theorem mem_dblSet_iff (hG2 : Stmt5_Gamma2) {G : Type} [Group G] [Finite G] {z : G}
    (hJ : HypJ4 G z) (c : Loc49 G z) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0)
    {d : G} (hd : d ∈ c.G3) :
    d ∈ dblSet c.G3 c.x0 y ↔ d • c.x0 = c.x0 ∨ d • c.x0 ∈ c.nbrP := by
  classical
  have hyN : y ∈ c.nbrP := c.mem_nbrP_of_mem_ptsL hy hyx
  have horb : MulAction.orbit ↥(c.G1.subgroupOf c.G3) y = c.nbrP :=
    c.orbit_subgroupOf_G1_eq_nbrP hG2 hJ hyN
  constructor
  · intro hdD
    rw [dblSet] at hdD
    obtain ⟨p, hp, j, hj, hpj⟩ := Set.mem_mul.mp hdD
    obtain ⟨i, hi, k, hk, hik⟩ := Set.mem_mul.mp hp
    obtain ⟨hiG3, hiS⟩ := Subgroup.mem_inf.mp hi
    obtain ⟨hjG3, hjS⟩ := Subgroup.mem_inf.mp hj
    obtain ⟨-, hkS⟩ := Subgroup.mem_inf.mp hk
    have hd_eq : d = i * k * j := by rw [← hpj, ← hik]
    have hky : k • c.x0 = c.x0 ∨ k • c.x0 = y := by
      have hk : k • ({c.x0, y} : Set (G ⧸ c.G1)) = {c.x0, y} := MulAction.mem_stabilizer_iff.mp hkS
      have hmem : k • c.x0 ∈ ({c.x0, y} : Set (G ⧸ c.G1)) := by
        rw [← hk]
        exact Set.smul_mem_smul_set (by simp)
      simpa using hmem
    have hiG1 : i ∈ c.G1 := by
      rw [← c.stab_x0]
      exact hiS
    have hiy : i • y ∈ c.nbrP := by
      rw [← horb]
      exact MulAction.mem_orbit y
        (⟨⟨i, hiG3⟩, by simpa [Subgroup.mem_subgroupOf] using hiG1⟩ :
          ↥(c.G1.subgroupOf c.G3))
    have hcalc : d • c.x0 = i • (k • c.x0) := by
      rw [hd_eq, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp hjS]
    rcases hky with hkx | hkx
    · left
      rw [hcalc, hkx, MulAction.mem_stabilizer_iff.mp hiS]
    · right
      rw [hcalc, hkx]
      exact hiy
  · rintro (hx | hx)
    · have hdA : d ∈ (c.G3 ⊓ stabilizer G c.x0 : Subgroup G) :=
        Subgroup.mem_inf.mpr ⟨hd, MulAction.mem_stabilizer_iff.mpr hx⟩
      have h1A : (1 : G) ∈ (c.G3 ⊓ stabilizer G c.x0 : Subgroup G) :=
        Subgroup.mem_inf.mpr ⟨c.G3.one_mem, MulAction.mem_stabilizer_iff.mpr (one_smul G _)⟩
      have h1B : (1 : G) ∈
          (c.G3 ⊓ stabilizer G ({c.x0, y} : Set (G ⧸ c.G1)) : Subgroup G) :=
        Subgroup.mem_inf.mpr ⟨c.G3.one_mem,
          MulAction.mem_stabilizer_iff.mpr (one_smul G _)⟩
      rw [dblSet]
      refine Set.mem_mul.mpr ⟨d * 1, ?_, 1, h1A, by simp⟩
      exact Set.mem_mul.mpr ⟨d, hdA, 1, h1B, by simp⟩
    · have hmem : d • c.x0 ∈ MulAction.orbit ↥(c.G1.subgroupOf c.G3) y := by
        rw [horb]
        exact hx
      obtain ⟨i, hi⟩ := hmem
      have hiG : ((i : ↥c.G3) : G) ∈ c.G1 ⊓ c.G3 := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp i.2, (i : ↥c.G3).2⟩
      have hiy : ((i : ↥c.G3) : G) • y = d • c.x0 := by
        simpa only [Subgroup.smul_def] using hi
      obtain ⟨σ, hσG3, hσx, hσy⟩ := c.exists_swap hG2 hJ hyN
      let j : G := σ⁻¹ * ((i : ↥c.G3) : G)⁻¹ * d
      have hjG3 : j ∈ c.G3 :=
        mul_mem (mul_mem (inv_mem hσG3) (inv_mem hiG.2)) hd
      have hjx : j • c.x0 = c.x0 := by
        calc j • c.x0
            = σ⁻¹ • (((i : ↥c.G3) : G)⁻¹ • (d • c.x0)) := by
              simp only [j]
              rw [mul_smul, mul_smul]
          _ = σ⁻¹ • (((i : ↥c.G3) : G)⁻¹ • (((i : ↥c.G3) : G) • y)) := by rw [← hiy]
          _ = σ⁻¹ • y := by rw [inv_smul_smul]
          _ = c.x0 := by rw [← hσx, inv_smul_smul]
      have hjA : j ∈ (c.G3 ⊓ stabilizer G c.x0 : Subgroup G) :=
        Subgroup.mem_inf.mpr ⟨hjG3, MulAction.mem_stabilizer_iff.mpr hjx⟩
      have hiA : ((i : ↥c.G3) : G) ∈ (c.G3 ⊓ stabilizer G c.x0 : Subgroup G) :=
        Subgroup.mem_inf.mpr ⟨hiG.2,
          MulAction.mem_stabilizer_iff.mpr (c.smul_x0_of_mem hiG.1)⟩
      have hσB : σ ∈
          (c.G3 ⊓ stabilizer G ({c.x0, y} : Set (G ⧸ c.G1)) : Subgroup G) :=
        Subgroup.mem_inf.mpr ⟨hσG3, by
          rw [MulAction.mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, hσx, hσy,
            Set.pair_comm]⟩
      have hd_eq : ((i : ↥c.G3) : G) * σ * j = d := by
        simp only [j]
        group
      rw [dblSet]
      refine Set.mem_mul.mpr ⟨((i : ↥c.G3) : G) * σ, ?_, j, hjA, hd_eq⟩
      exact Set.mem_mul.mpr ⟨((i : ↥c.G3) : G), hiA, σ, hσB, rfl⟩

theorem smul_x0_mem_nbrP_iff (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2)
    {G : Type} [Group G] [Finite G] {z : G}
    (hJ : HypJ4 G z) (c : Loc49 G z) (ρ : ResM24 c) (φ : ↥c.G3 ≃* ↥c.G3)
    (hφ : autPres c.G3 (c.G3 ⊓ stabilizer G c.x0) φ) (d : ↥c.G3) :
    (d : G) • c.x0 ∈ c.nbrP ↔ ((φ d : ↥c.G3) : G) • c.x0 ∈ c.nbrP := by
  classical
  let K : Subgroup ↥c.G3 := c.G1.subgroupOf c.G3
  have hmemK : ∀ a : ↥c.G3, a ∈ K ↔ (a : G) ∈ c.G3 ⊓ stabilizer G c.x0 := by
    intro a
    rw [Subgroup.mem_subgroupOf, c.stab_x0, inf_comm]
    exact ⟨fun h => ⟨h, a.2⟩, fun h => h.1⟩
  have hKL : K.map φ.toMonoidHom = K := by
    ext b
    rw [Subgroup.mem_map_equiv, hmemK (φ.symm b), hmemK b]
    simpa using hφ (φ.symm b)
  have hstab : (MulAction.stabilizer ↥c.G3 c.x0).map φ.toMonoidHom =
      MulAction.stabilizer ↥c.G3 c.x0 := by
    rw [← MulAction.stabilizer_subgroupOf c.G3 c.x0, c.stab_x0]
    exact hKL
  let α := ↥(MulAction.orbit ↥c.G3 c.x0)
  let x0α : α := ⟨c.x0, MulAction.mem_orbit_self c.x0⟩
  let Φ : α ≃ α := orbitEquivOfStabilizerMap φ c.x0 c.x0 hstab
  have hΦ_smul : ∀ (g : ↥c.G3) (x : α), Φ (g • x) = φ g • Φ x :=
    fun g x => orbitEquivOfStabilizerMap_smul φ c.x0 c.x0 hstab g x
  have hΦ_x0 : Φ x0α = x0α :=
    orbitEquivOfStabilizerMap_self φ c.x0 c.x0 hstab
  obtain ⟨y, hy⟩ : c.nbrP.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [c.ncard_nbrP ρ hLU hG2 hJ]; norm_num)
  have hyOrb : y ∈ MulAction.orbit ↥c.G3 c.x0 := by
    rw [← c.ptsP_eq_orbit]
    exact hy.1
  let yα : α := ⟨y, hyOrb⟩
  have horb : MulAction.orbit ↥K y = c.nbrP :=
    c.orbit_subgroupOf_G1_eq_nbrP hG2 hJ hy
  let N : Set α := MulAction.orbit ↥K yα
  have hNimg : ((fun a : α => (a : G ⧸ c.G1)) '' N) = c.nbrP := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨k, hk⟩ := hb
      rw [← hk]
      change ((k : ↥c.G3) : G) • y ∈ c.nbrP
      rw [← horb]
      exact MulAction.mem_orbit y k
    · intro ha
      have haK : a ∈ MulAction.orbit ↥K y := by rw [horb]; exact ha
      obtain ⟨k, hk⟩ := haK
      refine ⟨k • yα, MulAction.mem_orbit yα k, ?_⟩
      change ((k : ↥c.G3) : G) • y = a
      simpa [Subgroup.smul_def] using hk
  have hNcard : N.ncard = 60 := by
    have hinj : Set.InjOn (fun a : α => (a : G ⧸ c.G1)) N :=
      fun a _ b _ h => Subtype.ext h
    calc N.ncard = ((fun a : α => (a : G ⧸ c.G1)) '' N).ncard :=
          (Set.InjOn.ncard_image (f := fun a : α => (a : G ⧸ c.G1)) (s := N) hinj).symm
      _ = c.nbrP.ncard := by rw [hNimg]
      _ = 60 := c.ncard_nbrP ρ hLU hG2 hJ
  have hcardα : Nat.card α = 77 := by
    rw [Nat.card_coe_set_eq, ← c.ptsP_eq_orbit]
    exact c.ncard_ptsP ρ hLU hG2 hJ
  have hyα : yα ∈ MulAction.orbit ↥c.G3 x0α := by
    obtain ⟨g, hg⟩ := hyOrb
    have hg' : g • x0α = yα := Subtype.ext hg
    rw [← hg']
    exact MulAction.mem_orbit x0α g
  have hΦ : ∀ (g : ↥c.G3) {x : α}, x ∈ MulAction.orbit ↥c.G3 x0α →
      Φ (g • x) = φ g • Φ x := fun g x _ => hΦ_smul g x
  have hΦ_inj : Set.InjOn Φ (MulAction.orbit ↥c.G3 x0α) :=
    fun a _ b _ h => Φ.injective h
  have hO_orbit : Φ '' N = MulAction.orbit ↥K (Φ yα) := by
    have h := image_orbit_of_map_eq (e := φ) (Φ := Φ) (a := x0α) (y := yα)
      (K := K) (L := K) hKL hΦ hΦ_inj hyα
    simpa [N] using h
  have hOcard : (Φ '' N).ncard = 60 := by
    rw [Set.InjOn.ncard_image (f := Φ) (s := N) (fun a _ b _ h => Φ.injective h), hNcard]
  have hnon : (N ∩ Φ '' N).Nonempty := by
    apply Set.nonempty_inter_of_lt_ncard_add_ncard
    rw [hcardα, hNcard, hOcard]
    norm_num
  obtain ⟨a, haN, haO⟩ := hnon
  have hN_eq : N = Φ '' N := by
    calc N = MulAction.orbit ↥K yα := rfl
      _ = MulAction.orbit ↥K a := (MulAction.orbit_eq_iff.mpr haN).symm
      _ = MulAction.orbit ↥K (Φ yα) :=
          MulAction.orbit_eq_iff.mpr (by rwa [hO_orbit] at haO)
      _ = Φ '' N := hO_orbit.symm
  have hmem_iff : ∀ x : α, x ∈ N ↔ Φ x ∈ N := by
    intro x
    constructor
    · intro hx
      exact hN_eq.symm ▸ ⟨x, hx, rfl⟩
    · intro hx
      have hx' : Φ x ∈ Φ '' N := hN_eq ▸ hx
      obtain ⟨z, hz, hzx⟩ := hx'
      have hzx' : z = x := Φ.injective hzx
      rwa [← hzx']
  have hNmem : ∀ x : α, x ∈ N ↔ (x : G ⧸ c.G1) ∈ c.nbrP := by
    intro x
    rw [show N = MulAction.orbit ↥K yα from rfl, ← horb]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      change ((k : ↥c.G3) : G) • y = x
      have h := congrArg (fun a : α => (a : G ⧸ c.G1)) hk
      change ((k : ↥c.G3) : G) • y = (x : G ⧸ c.G1) at h
      simpa [Subgroup.smul_def] using h
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
  have hx : Φ (d • x0α) = (φ d) • x0α := by
    rw [hΦ_smul d x0α, hΦ_x0]
  have hmem := hmem_iff (d • x0α)
  rw [hx, hNmem (d • x0α), hNmem ((φ d) • x0α)] at hmem
  have hcoe_d : ((d • x0α : α) : G ⧸ c.G1) = (d : G) • c.x0 := by
    rfl
  have hcoe_φd : (((φ d) • x0α : α) : G ⧸ c.G1) =
      ((φ d : ↥c.G3) : G) • c.x0 := by
    rfl
  rwa [hcoe_d, hcoe_φd] at hmem

theorem hypV_v3 (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2)
    {G : Type} [Group G] [Finite G] {z : G}
    (hJ : HypJ4 G z) (c : Loc49 G z) (ρ : ResM24 c) {y : G ⧸ c.G1} (hy : y ∈ c.ptsL)
    (hyx : y ≠ c.x0) :
    ∀ φ : ↥c.G3 ≃* ↥c.G3, autPres c.G3 (c.G3 ⊓ stabilizer G c.x0) φ →
      ∃ φ₁ φ₂ : ↥c.G3 ≃* ↥c.G3,
        (∀ d : ↥c.G3, (d : G) ∈ dblSet c.G3 c.x0 y ↔
          ((φ₁ d : ↥c.G3) : G) ∈ dblSet c.G3 c.x0 y) ∧
        autFix c.G3 (c.G3 ⊓ stabilizer G c.x0) φ₂ ∧
        ∀ i : ↥c.G3, ((φ i : ↥c.G3) : G) = φ₁ (φ₂ i) := by
  intro φ hφ
  refine ⟨φ, MulEquiv.refl ↥c.G3, ?_, ?_, ?_⟩
  · intro d
    rw [c.mem_dblSet_iff hG2 hJ hy hyx d.2,
      c.mem_dblSet_iff hG2 hJ hy hyx (φ d).2,
      c.smul_x0_eq_iff_of_autPres hφ d,
      c.smul_x0_mem_nbrP_iff hLU hG2 hJ ρ φ hφ d]
  · intro a ha
    rfl
  · intro i
    rfl

end Loc49

end CFSG.Quasithin.H13.AS91
