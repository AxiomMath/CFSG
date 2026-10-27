module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LieType.BorelTits.Basic
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section HallWitt

variable {G : Type} [Group G]

theorem szN4_commutator_commutator_mem {N : Subgroup G} {x y z : G}
    (hx : ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hy : ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hz : ∀ n ∈ N, z * n * z⁻¹ ∈ N)
    (h1 : ⁅⁅z⁻¹, x⁻¹⁆, y⁆ ∈ N) (h2 : ⁅⁅y⁻¹, z⁆, x⁻¹⁆ ∈ N) : ⁅⁅x, y⁆, z⁆ ∈ N := by
  have key := conj_commutatorElement_left_commutatorElement_mul x⁻¹ y z
  rw [inv_inv] at key
  have hA : z * ⁅⁅z⁻¹, x⁻¹⁆, y⁆ * z⁻¹ ∈ N := hz _ h1
  have hB : y * ⁅⁅y⁻¹, z⁆, x⁻¹⁆ * y⁻¹ ∈ N := hy _ h2
  have h3 : x⁻¹ * ⁅⁅x, y⁆, z⁆ * x =
      ((z * ⁅⁅z⁻¹, x⁻¹⁆, y⁆ * z⁻¹) * (y * ⁅⁅y⁻¹, z⁆, x⁻¹⁆ * y⁻¹))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [mul_assoc] using key
  have e : ⁅⁅x, y⁆, z⁆ =
      x * ((z * ⁅⁅z⁻¹, x⁻¹⁆, y⁆ * z⁻¹) * (y * ⁅⁅y⁻¹, z⁆, x⁻¹⁆ * y⁻¹))⁻¹ * x⁻¹ := by
    rw [← h3]; group
  rw [e]
  exact hx _ (N.inv_mem (N.mul_mem hA hB))

end HallWitt

section Block

variable {G : Type} [Group G]

theorem szN4_mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  show Subgroup.map (MulAut.conj g).toMonoidHom ⁅A, B⁆ = ⁅A, B⁆
  rw [Subgroup.map_commutator]
  exact congrArg₂ (fun A B => ⁅A, B⁆) hA hB

theorem szN4_mem_normalizer_blockU {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer (blockU L : Set G) :=
  szN4_mem_normalizer_commutator (normalizer_le_normalizer_pCoreOf 2 L hg) hg

theorem szN4_blockU_le {L : Subgroup G} : blockU L ≤ L := by
  rw [blockU, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₁L : g₁ ∈ L := pCoreOf_le 2 L hg₁
  rw [commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem hg₁L hg₂) (inv_mem hg₁L)) (inv_mem hg₂)

theorem szN4_blockU_le_pCoreOf {L : Subgroup G} : blockU L ≤ pCoreOf 2 L := by
  rw [blockU, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have hg₁' : g₁ ∈ pCoreOf 2 L := hg₁
  have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ pCoreOf 2 L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hg₂) _).mp (inv_mem hg₁')
  have h2 := mul_mem hg₁' h1
  have e : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact h2

theorem szN4_inv_comm_mem {L : Subgroup G} {c : G} (hcN : c ∈ Subgroup.normalizer (L : Set G))
    (hcQ : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L) :
    ∀ x ∈ L, c⁻¹ * x * c * x⁻¹ ∈ pCoreOf 2 L := by
  intro x hx
  have hw : c⁻¹ * x * c ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hcN) x).mp hx
    simpa using this
  have h := hcQ _ hw
  have e : c * (c⁻¹ * x * c) * c⁻¹ * (c⁻¹ * x * c)⁻¹ = (c⁻¹ * x * c * x⁻¹)⁻¹ := by group
  rw [e] at h
  simpa using inv_mem h

end Block


section PerfectStep

variable {G : Type} [Group G]

theorem szN4_conj_comm_mem_blockU {L : Subgroup G} {c : G} (hperf : ⁅L, L⁆ = L)
    (hcN : c ∈ Subgroup.normalizer (L : Set G))
    (hcQ : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L) :
    ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ blockU L := by
  have hUN : ∀ g, g ∈ Subgroup.normalizer (L : Set G) → ∀ n ∈ blockU L, g * n * g⁻¹ ∈ blockU L :=
    fun g hg n hn => (Subgroup.mem_normalizer_iff.mp (szN4_mem_normalizer_blockU hg) n).mp hn
  have hcQ' := szN4_inv_comm_mem hcN hcQ
  let K : Subgroup G :=
    { carrier := {g | g ∈ L ∧ c * g * c⁻¹ * g⁻¹ ∈ blockU L}
      one_mem' := ⟨L.one_mem, by simp⟩
      mul_mem' := by
        rintro g h ⟨hgL, hg⟩ ⟨hhL, hh⟩
        refine ⟨L.mul_mem hgL hhL, ?_⟩
        have e : c * (g * h) * c⁻¹ * (g * h)⁻¹ =
            (c * g * c⁻¹ * g⁻¹) * (g * (c * h * c⁻¹ * h⁻¹) * g⁻¹) := by group
        rw [e]
        exact (blockU L).mul_mem hg (hUN g (Subgroup.le_normalizer hgL) _ hh)
      inv_mem' := by
        rintro g ⟨hgL, hg⟩
        refine ⟨L.inv_mem hgL, ?_⟩
        have e : c * g⁻¹ * c⁻¹ * (g⁻¹)⁻¹ = g⁻¹ * (c * g * c⁻¹ * g⁻¹)⁻¹ * g := by group
        rw [e]
        have h1 : (c * g * c⁻¹ * g⁻¹)⁻¹ ∈ blockU L := (blockU L).inv_mem hg
        have := hUN g⁻¹ (Subgroup.le_normalizer (L.inv_mem hgL)) _ h1
        simpa using this }
  have hKc : ⁅L, L⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)
    refine ⟨hxy, ?_⟩
    have hxN := hUN x (Subgroup.le_normalizer hx)
    have hyN := hUN y (Subgroup.le_normalizer hy)
    have h1 : ⁅⁅c⁻¹, x⁻¹⁆, y⁆ ∈ blockU L := by
      have hq : ⁅c⁻¹, x⁻¹⁆ ∈ pCoreOf 2 L := by
        have := hcQ' x⁻¹ (L.inv_mem hx)
        simpa [commutatorElement_def] using this
      exact Subgroup.commutator_mem_commutator hq hy
    have h2 : ⁅⁅y⁻¹, c⁆, x⁻¹⁆ ∈ blockU L := by
      have hq : ⁅y⁻¹, c⁆ ∈ pCoreOf 2 L := by
        have h3 := hcQ y⁻¹ (L.inv_mem hy)
        have e : ⁅y⁻¹, c⁆ = (c * y⁻¹ * c⁻¹ * (y⁻¹)⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact inv_mem h3
      exact Subgroup.commutator_mem_commutator hq (L.inv_mem hx)
    have h3 := szN4_commutator_commutator_mem hxN hyN (hUN c hcN) h1 h2
    have e : c * ⁅x, y⁆ * c⁻¹ * ⁅x, y⁆⁻¹ = (⁅⁅x, y⁆, c⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (blockU L).inv_mem h3
  intro x hx
  have : x ∈ K := hKc (by rw [hperf]; exact hx)
  exact this.2

end PerfectStep


section UEqComm

variable {G : Type} [Group G]

theorem szN4_blockU_le_commutator {L : Subgroup G} (hperf : ⁅L, L⁆ = L) :
    blockU L ≤ ⁅blockU L, L⁆ := by
  set N : Subgroup G := ⁅blockU L, L⁆ with hN
  have hNn : ∀ g ∈ L, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp (szN4_mem_normalizer_commutator
      (szN4_mem_normalizer_blockU (Subgroup.le_normalizer hg)) (Subgroup.le_normalizer hg)) n).mp hn
  let K : Subgroup G :=
    { carrier := {g | g ∈ L ∧ ∀ q ∈ pCoreOf 2 L, ⁅g, q⁆ ∈ N}
      one_mem' := ⟨L.one_mem, fun q _ => by simp⟩
      mul_mem' := by
        rintro g h ⟨hgL, hg⟩ ⟨hhL, hh⟩
        refine ⟨L.mul_mem hgL hhL, fun q hq => ?_⟩
        have e : ⁅g * h, q⁆ = g * ⁅h, q⁆ * g⁻¹ * ⁅g, q⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem (hNn g hgL _ (hh q hq)) (hg q hq)
      inv_mem' := by
        rintro g ⟨hgL, hg⟩
        refine ⟨L.inv_mem hgL, fun q hq => ?_⟩
        have e : ⁅g⁻¹, q⁆ = g⁻¹ * (⁅g, q⁆)⁻¹ * g := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hNn g⁻¹ (L.inv_mem hgL) _ (N.inv_mem (hg q hq)) |> fun h => by simpa using h }
  have hKc : ⁅L, L⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)
    refine ⟨hxy, fun q hq => ?_⟩
    have hqL : q ∈ L := pCoreOf_le 2 L hq
    have h1 : ⁅⁅q⁻¹, x⁻¹⁆, y⁆ ∈ N :=
      Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator (inv_mem hq) (L.inv_mem hx)) hy
    have h2 : ⁅⁅y⁻¹, q⁆, x⁻¹⁆ ∈ N := by
      have hu : ⁅y⁻¹, q⁆ ∈ blockU L := by
        have e : ⁅y⁻¹, q⁆ = (⁅q, y⁻¹⁆)⁻¹ := by simp only [commutatorElement_def]; group
        rw [e]
        exact (blockU L).inv_mem (Subgroup.commutator_mem_commutator hq (L.inv_mem hy))
      exact Subgroup.commutator_mem_commutator hu (L.inv_mem hx)
    exact szN4_commutator_commutator_mem (hNn x hx) (hNn y hy) (hNn q hqL) h1 h2
  rw [blockU, Subgroup.commutator_le]
  intro q hq g hg
  have hgK : g ∈ K := hKc (by rw [hperf]; exact hg)
  have h := hgK.2 q hq
  have e : ⁅q, g⁆ = (⁅g, q⁆)⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact N.inv_mem h

end UEqComm


section Scalar

open Matrix

variable {F : Type} [Field F]

theorem szN4_scalar_of_commute (Θ : (Fin 2 → F) → (Fin 2 → F))
    (hadd : ∀ v w, Θ (v + w) = Θ v + Θ w)
    (hcomm : ∀ A : SpecialLinearGroup (Fin 2) F, ∀ v,
      Θ ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) = (A : Matrix (Fin 2) (Fin 2) F).mulVec (Θ v)) :
    ∃ a : F, ∀ v, Θ v = a • v := by
  have hΘ0 : Θ 0 = 0 := by
    have h := hadd 0 0
    simpa using h
  let t : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let w : SpecialLinearGroup (Fin 2) F := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  let d : ∀ x : F, x ≠ 0 → SpecialLinearGroup (Fin 2) F := fun x hx =>
    ⟨!![x, 0; 0, x⁻¹], by simp [Matrix.det_fin_two, hx]⟩
  let e0 : Fin 2 → F := ![1, 0]
  let e1 : Fin 2 → F := ![0, 1]
  have ht : (t : Matrix (Fin 2) (Fin 2) F).mulVec e0 = e0 := by
    ext i; fin_cases i <;> simp [t, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hw : (w : Matrix (Fin 2) (Fin 2) F).mulVec e0 = e1 := by
    ext i; fin_cases i <;> simp [w, e0, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hd0 : ∀ (x : F) (hx : x ≠ 0), (d x hx : Matrix (Fin 2) (Fin 2) F).mulVec e0 = x • e0 := by
    intro x hx
    ext i; fin_cases i <;> simp [d, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hd1 : ∀ (x : F) (hx : x ≠ 0), (d x hx : Matrix (Fin 2) (Fin 2) F).mulVec e1 = x⁻¹ • e1 := by
    intro x hx
    ext i; fin_cases i <;> simp [d, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  set p := Θ e0 0 with hp
  have hq : Θ e0 1 = 0 := by
    have h := hcomm t e0
    rw [ht] at h
    have h0 := congrFun h 0
    simp only [t, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    simpa using h0
  have hΘe0 : Θ e0 = p • e0 := by
    ext i; fin_cases i <;> simp [hp, e0, hq]
  have hΘe1 : Θ e1 = p • e1 := by
    have h := hcomm w e0
    rw [hw, hΘe0] at h
    rw [h]
    ext i; fin_cases i <;> simp [w, e1, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hΘ0x : ∀ x : F, Θ (x • e0) = p • (x • e0) := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [hΘ0]
    · have h := hcomm (d x hx) e0
      rw [hd0 x hx, hΘe0] at h
      rw [h]
      ext i; fin_cases i <;> simp [d, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  have hΘ1x : ∀ y : F, Θ (y • e1) = p • (y • e1) := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp [hΘ0]
    · have hy' : y⁻¹ ≠ 0 := inv_ne_zero hy
      have h := hcomm (d y⁻¹ hy') e1
      rw [hd1 y⁻¹ hy', inv_inv, hΘe1] at h
      rw [h]
      ext i; fin_cases i <;> simp [d, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  refine ⟨p, fun v => ?_⟩
  have hv : v = v 0 • e0 + v 1 • e1 := by
    ext i; fin_cases i <;> simp [e0, e1]
  rw [hv, hadd, hΘ0x, hΘ1x]
  ext i; fin_cases i <;> simp [e0, e1]

end Scalar


section PCoreBridge

theorem szN4_mem_pCore_iff {G : Type} [Group G] {L : Subgroup G} (x : ↥L) :
    x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L := (CFSG.mem_openPCoreOf_iff x).symm

end PCoreBridge

section Quotient

variable {G : Type} [Group G]

theorem szN4_conj_mem_centralizer {L : Subgroup G} {g z : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hz : z ∈ Subgroup.centralizer (L : Set G)) :
    g * z * g⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) l).mp hl
    simpa using this
  have h2 := Subgroup.mem_centralizer_iff.mp hz _ h1
  calc l * (g * z * g⁻¹) = g * ((g⁻¹ * l * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * l * g)) * g⁻¹ := by rw [h2]
    _ = g * z * g⁻¹ * l := by group

theorem szN4_lin2_trivial_on_quot {L : Subgroup G} {n : ℕ} (hlin : IsLin2Type L n)
    {c : G} (hcN : c ∈ Subgroup.normalizer (L : Set G))
    (hcQ : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L)
    (hfix : ∃ u ∈ blockU L, u ∉ Subgroup.centralizer (L : Set G) ∧
      c * u * c⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    ∀ u ∈ blockU L, c * u * c⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, β, hβs, hβk, hβc⟩ := hlin
  have hcU : ∀ u ∈ blockU L, c * u * c⁻¹ ∈ blockU L := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (szN4_mem_normalizer_blockU hcN) u).mp hu
  let φ : ↥(blockU L) →* ↥(blockU L) :=
    { toFun := fun u => ⟨c * u * c⁻¹, hcU u u.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have hker : β.ker ≤ (β.comp φ).ker := by
    intro u hu
    rw [hβk] at hu
    have hu' : (u : G) ∈ blockZ L := Subgroup.mem_subgroupOf.mp hu
    rw [MonoidHom.mem_ker]
    show β (φ u) = 1
    have : φ u ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact ⟨hcU u u.2, szN4_conj_mem_centralizer hcN hu'.2⟩
    exact MonoidHom.mem_ker.mp this
  let Θ' : Multiplicative (Fin 2 → F) →* Multiplicative (Fin 2 → F) :=
    (MonoidHom.liftOfRightInverse β (Function.surjInv hβs) (Function.rightInverse_surjInv hβs))
      ⟨β.comp φ, hker⟩
  have hΘ'β : ∀ u : ↥(blockU L), Θ' (β u) = β (φ u) := fun u => by
    simp [Θ', MonoidHom.liftOfRightInverse_comp_apply]
  let Θ : (Fin 2 → F) → (Fin 2 → F) := fun v => Multiplicative.toAdd (Θ' (Multiplicative.ofAdd v))
  have hΘ : ∀ u : ↥(blockU L),
      Θ (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (φ u)) := by
    intro u
    simp only [Θ, ofAdd_toAdd]
    rw [hΘ'β]
  have hadd : ∀ v w, Θ (v + w) = Θ v + Θ w := by
    intro v w
    simp only [Θ]
    rw [ofAdd_add, map_mul, toAdd_mul]
  have hcomm : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, ∀ v : Fin 2 → F,
      Θ ((A : Matrix (Fin 2) (Fin 2) F).mulVec v) =
        (A : Matrix (Fin 2) (Fin 2) F).mulVec (Θ v) := by
    intro A v
    obtain ⟨ℓ, rfl⟩ := hαs A
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
    have hℓN : (ℓ : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer ℓ.2
    have hu'mem : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (szN4_mem_normalizer_blockU hℓN) u).mp u.2
    let u' : ↥(blockU L) := ⟨(ℓ : G) * u * (ℓ : G)⁻¹, hu'mem⟩
    have h1 : Multiplicative.toAdd (β u') = (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec v := by
      rw [hβc ℓ u u' rfl, hu]; simp
    have hℓ'L : c * (ℓ : G) * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hcN (ℓ : G)).mp ℓ.2
    let ℓ' : ↥L := ⟨c * (ℓ : G) * c⁻¹, hℓ'L⟩
    have hαℓ' : α ℓ' = α ℓ := by
      have hmem : ℓ' * ℓ⁻¹ ∈ α.ker := by
        rw [hαk, szN4_mem_pCore_iff]
        exact hcQ (ℓ : G) ℓ.2
      have := MonoidHom.mem_ker.mp hmem
      rw [map_mul, map_inv, mul_inv_eq_one] at this
      exact this
    have h2 : Multiplicative.toAdd (β (φ u')) =
        (α ℓ' : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β (φ u))) := by
      refine hβc ℓ' (φ u) (φ u') ?_
      show c * ((ℓ : G) * u * (ℓ : G)⁻¹) * c⁻¹ =
        (c * (ℓ : G) * c⁻¹) * (c * (u : G) * c⁻¹) * (c * (ℓ : G) * c⁻¹)⁻¹
      group
    calc Θ ((α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec v) = Θ (Multiplicative.toAdd (β u')) := by
          rw [h1]
      _ = Multiplicative.toAdd (β (φ u')) := hΘ u'
      _ = (α ℓ' : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β (φ u))) := h2
      _ = (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Θ v) := by
          rw [hαℓ', ← hΘ u, hu]; simp
  obtain ⟨a, ha⟩ := szN4_scalar_of_commute Θ hadd hcomm
  obtain ⟨u₀, hu₀U, hu₀C, hu₀fix⟩ := hfix
  let u₀' : ↥(blockU L) := ⟨u₀, hu₀U⟩
  have hβu₀ : β (φ u₀') = β u₀' := by
    have hm : φ u₀' * u₀'⁻¹ ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact ⟨(blockU L).mul_mem (hcU u₀ hu₀U) ((blockU L).inv_mem hu₀U), hu₀fix⟩
    have := MonoidHom.mem_ker.mp hm
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have hβne : β u₀' ≠ 1 := by
    intro h
    apply hu₀C
    have : u₀' ∈ β.ker := h
    rw [hβk, Subgroup.mem_subgroupOf] at this
    exact this.2
  have ha1 : a = 1 := by
    have h1 := hΘ u₀'
    rw [hβu₀, ha] at h1
    obtain ⟨i, hi⟩ : ∃ i, Multiplicative.toAdd (β u₀') i ≠ 0 := by
      by_contra hno
      push Not at hno
      apply hβne
      have h0 : Multiplicative.toAdd (β u₀') = 0 := funext hno
      exact Multiplicative.toAdd.injective h0
    have h2 := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have h3 : (a - 1) * Multiplicative.toAdd (β u₀') i = 0 := by
      rw [sub_mul, h2, one_mul, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd h4 hi
  intro u hu
  let u' : ↥(blockU L) := ⟨u, hu⟩
  have h1 := hΘ u'
  rw [ha, ha1, one_smul] at h1
  have hβeq : β (φ u') = β u' := (Multiplicative.toAdd.injective h1).symm
  have hm : φ u' * u'⁻¹ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβeq, mul_inv_cancel]
  rw [hβk, Subgroup.mem_subgroupOf] at hm
  exact hm.2

end Quotient

section Main

variable {G : Type} [Group G]

theorem szN4_eq_one_of_mem_pCoreOf_of_pow {L : Subgroup G} [Finite G] {u : G} (hu : u ∈ pCoreOf 2 L) {m : ℕ}
    (hm : Odd m) (hum : u ^ m = 1) : u = 1 := by
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨u, hu⟩
  have hu2 : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hd1 : orderOf u ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hu2
  have hd2 : orderOf u ∣ m := orderOf_dvd_of_pow_eq_one hum
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm)
  have : orderOf u ∣ Nat.gcd m (2 ^ k) := Nat.dvd_gcd hd2 hd1
  rw [hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem szN4_lin2_central_of_fixed [Finite G] {L : Subgroup G} {n : ℕ} (hsh : IsShort2 L) (hlin : IsLin2Type L n)
    (hperf : ⁅L, L⁆ = L) {c : G} (hcN : c ∈ Subgroup.normalizer (L : Set G)) (hco : Odd (orderOf c))
    (hcQ : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L)
    (hfix : ∃ u ∈ blockU L, u ∉ Subgroup.centralizer (L : Set G) ∧
      c * u * c⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G)) :
    c ∈ Subgroup.centralizer (L : Set G) := by
  have hU := szN4_conj_comm_mem_blockU hperf hcN hcQ
  have hZ := szN4_lin2_trivial_on_quot hlin hcN hcQ hfix
  have hUQ : blockU L ≤ pCoreOf 2 L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) := hsh.2.2.1.1
  have hUab : ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hUQ ha).2 b (szN4_blockU_le_pCoreOf hb)).symm
  have hUL : blockU L ≤ L := szN4_blockU_le
  have hUnorm : ∀ g ∈ L, ∀ n ∈ blockU L, g * n * g⁻¹ ∈ blockU L := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.mp (szN4_mem_normalizer_blockU (Subgroup.le_normalizer hg)) n).mp hn
  have hcomm : ⁅blockU L, L⁆ ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu x hx
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    rw [Set.mem_singleton_iff] at hd
    subst hd
    set z : G := d * u * d⁻¹ * u⁻¹ with hzdef
    set e : G := d * x * d⁻¹ * x⁻¹ with hedef
    have hzC : z ∈ Subgroup.centralizer (L : Set G) := hZ u hu
    have heU : e ∈ blockU L := hU x hx
    have hzu : d * u * d⁻¹ = z * u := by rw [hzdef]; group
    have hex : d * x * d⁻¹ = e * x := by rw [hedef]; group
    have hzcomm : ∀ y ∈ L, z * y = y * z := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hzC y hy).symm
    have hconj : d * ⁅u, x⁆ * d⁻¹ = ⁅z * u, e * x⁆ := by
      have : d * ⁅u, x⁆ * d⁻¹ = ⁅d * u * d⁻¹, d * x * d⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [this, hzu, hex]
    have hue : u * e = e * u := hUab u hu e heU
    have hux : ⁅u, x⁆ ∈ blockU L := by
      have h1 : u * (x * u⁻¹ * x⁻¹) ∈ blockU L :=
        (blockU L).mul_mem hu (hUnorm x hx _ ((blockU L).inv_mem hu))
      have e1 : ⁅u, x⁆ = u * (x * u⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
      rw [e1]; exact h1
    have hecomm : e * ⁅u, x⁆ = ⁅u, x⁆ * e := hUab e heU _ hux
    have hzL : z * (u * e * x * u⁻¹) = (u * e * x * u⁻¹) * z :=
      hzcomm _ (L.mul_mem (L.mul_mem (L.mul_mem (hUL hu) (hUL heU)) hx) (L.inv_mem (hUL hu)))
    show d * ⁅u, x⁆ = ⁅u, x⁆ * d
    have hconj' : d * ⁅u, x⁆ * d⁻¹ = ⁅u, x⁆ := by
      rw [hconj]
      calc ⁅z * u, e * x⁆ = z * (u * e * x * u⁻¹) * z⁻¹ * x⁻¹ * e⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = (u * e * x * u⁻¹) * x⁻¹ * e⁻¹ := by
            rw [hzL]; group
        _ = e * ⁅u, x⁆ * e⁻¹ := by
            have : u * e * x * u⁻¹ * x⁻¹ * e⁻¹ = e * (u * x * u⁻¹ * x⁻¹) * e⁻¹ := by
              rw [show u * e * x * u⁻¹ * x⁻¹ * e⁻¹ = (u * e) * x * u⁻¹ * x⁻¹ * e⁻¹ by group, hue]; group
            rw [this]; simp only [commutatorElement_def]
        _ = ⁅u, x⁆ := by rw [hecomm]; group
    calc d * ⁅u, x⁆ = (d * ⁅u, x⁆ * d⁻¹) * d := by group
      _ = ⁅u, x⁆ * d := by rw [hconj']
  have hcU : ∀ u ∈ blockU L, c * u = u * c := by
    intro u hu
    have hu' : u ∈ ⁅blockU L, L⁆ := szN4_blockU_le_commutator hperf hu
    exact Subgroup.mem_centralizer_iff.mp (hcomm hu') c (Set.mem_singleton c)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  set m := orderOf c with hm
  have hcm : c ^ m = 1 := pow_orderOf_eq_one c
  have huU : x * c * x⁻¹ * c⁻¹ ∈ blockU L := by
    have h := (blockU L).inv_mem (hU x hx)
    have e1 : (c * x * c⁻¹ * x⁻¹)⁻¹ = x * c * x⁻¹ * c⁻¹ := by group
    rwa [e1] at h
  have hxc : x * c * x⁻¹ = (x * c * x⁻¹ * c⁻¹) * c := by group
  have hpow : (x * c * x⁻¹) ^ m = 1 := by
    rw [conj_pow, hcm]; group
  have hcomc : Commute (x * c * x⁻¹ * c⁻¹) c := (hcU _ huU).symm
  have hum : (x * c * x⁻¹ * c⁻¹) ^ m = 1 := by
    rw [hxc, hcomc.mul_pow, hcm, mul_one] at hpow
    exact hpow
  have hu1 : x * c * x⁻¹ * c⁻¹ = 1 :=
    szN4_eq_one_of_mem_pCoreOf_of_pow (szN4_blockU_le_pCoreOf huU) hco hum
  calc x * c = (x * c * x⁻¹ * c⁻¹) * (c * x) := by group
    _ = c * x := by rw [hu1, one_mul]

end Main

end CFSG.Quasithin
