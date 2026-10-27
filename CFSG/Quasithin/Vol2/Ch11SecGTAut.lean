module

public import CFSG.Quasithin.Vol2.Ch11SecGTSL2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open scoped MatrixGroups

namespace AutFit

variable {X : Type} [Group X]

theorem comm_of_mem_center {c : X} (hc : c ∈ Subgroup.center X) (g : X) : g * c = c * g :=
  Subgroup.mem_center_iff.mp hc g

theorem conj_of_mem_center {c : X} (hc : c ∈ Subgroup.center X) (g : X) : g * c * g⁻¹ = c := by
  rw [comm_of_mem_center hc g, mul_inv_cancel_right]

@[expose] def centSec (F : Subgroup X) (hF : F.Normal) : Subgroup X where
  carrier := {y | ∀ f ∈ F, y * f * y⁻¹ * f⁻¹ ∈ Subgroup.center X}
  one_mem' := fun f _ => by simp
  mul_mem' := by
    intro y₁ y₂ h₁ h₂ f hf
    have e : y₁ * y₂ * f * (y₁ * y₂)⁻¹ * f⁻¹ =
        (y₁ * (y₂ * f * y₂⁻¹ * f⁻¹) * y₁⁻¹) * (y₁ * f * y₁⁻¹ * f⁻¹) := by group
    rw [e, conj_of_mem_center (h₂ f hf)]
    exact mul_mem (h₂ f hf) (h₁ f hf)
  inv_mem' := by
    intro y h f hf
    have hf' : y⁻¹ * f * y ∈ F := by simpa using hF.conj_mem f hf y⁻¹
    have e : y⁻¹ * f * y⁻¹⁻¹ * f⁻¹ = (y * (y⁻¹ * f * y) * y⁻¹ * (y⁻¹ * f * y)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (h _ hf')

theorem centSec_normal (F : Subgroup X) (hF : F.Normal) : (centSec F hF).Normal := by
  refine ⟨fun y hy x f hf => ?_⟩
  have hf' : x⁻¹ * f * x ∈ F := by simpa using hF.conj_mem f hf x⁻¹
  have e : x * y * x⁻¹ * f * (x * y * x⁻¹)⁻¹ * f⁻¹ =
      x * (y * (x⁻¹ * f * x) * y⁻¹ * (x⁻¹ * f * x)⁻¹) * x⁻¹ := by group
  rw [e, conj_of_mem_center (hy _ hf')]
  exact hy _ hf'

theorem pow_card_mem_centralizer [Finite X] {F : Subgroup X} {hF : F.Normal}
    (hZF : Subgroup.center X ≤ F) {y : X} (hy : y ∈ centSec F hF) :
    y ^ Nat.card F ∈ Subgroup.centralizer (F : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hc : y * f * y⁻¹ * f⁻¹ ∈ Subgroup.center X := hy f hf
  obtain ⟨c, hcdef⟩ : ∃ c, c = y * f * y⁻¹ * f⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hc
  have hyf : y * f * y⁻¹ = c * f := by rw [hcdef]; group
  have hpow : ∀ n : ℕ, y ^ n * f * (y ^ n)⁻¹ = c ^ n * f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcn : c ^ n ∈ Subgroup.center X := pow_mem hc n
      calc y ^ (n + 1) * f * (y ^ (n + 1))⁻¹ = y * (y ^ n * f * (y ^ n)⁻¹) * y⁻¹ := by
            rw [pow_succ']
            group
        _ = (y * c ^ n * y⁻¹) * (y * f * y⁻¹) := by rw [ih]; group
        _ = c ^ n * (c * f) := by rw [conj_of_mem_center hcn, hyf]
        _ = c ^ (n + 1) * f := by rw [pow_succ, mul_assoc]
  have hcF : c ^ Nat.card F = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (G := F) (x := ⟨c, hZF hc⟩))
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have h := hpow (Nat.card F)
  rw [hcF, one_mul] at h
  calc f * y ^ Nat.card F = y ^ Nat.card F * f * (y ^ Nat.card F)⁻¹ * y ^ Nat.card F := by
        rw [h]
    _ = y ^ Nat.card F * f := by group

theorem map_mem_center (α : MulAut X) {z : X} (hz : z ∈ Subgroup.center X) :
    α z ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := α.surjective g
  rw [← map_mul, ← map_mul, comm_of_mem_center hz]

theorem inv_mul_mem_centSec {F : Subgroup X} (hF : F.Normal) {α : MulAut X}
    (hαF : ∀ f ∈ F, α f * f⁻¹ ∈ Subgroup.center X) (x : X) : x⁻¹ * α x ∈ centSec F hF := by
  intro f hf
  have hf' : x * f * x⁻¹ ∈ F := hF.conj_mem f hf x
  obtain ⟨c, hc, hcf⟩ : ∃ c ∈ Subgroup.center X, α f = c * f := ⟨_, hαF f hf, by group⟩
  obtain ⟨c', hc', hcf'⟩ : ∃ c' ∈ Subgroup.center X, α (x * f * x⁻¹) = c' * (x * f * x⁻¹) :=
    ⟨_, hαF _ hf', by group⟩
  have h1 : α x * f * (α x)⁻¹ = c⁻¹ * c' * (x * f * x⁻¹) := by
    have h2 : α (x * f * x⁻¹) = c * (α x * f * (α x)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hcf]
      calc α x * (c * f) * (α x)⁻¹ = (α x * c * (α x)⁻¹) * (α x * f * (α x)⁻¹) := by group
        _ = c * (α x * f * (α x)⁻¹) := by rw [conj_of_mem_center hc]
    rw [hcf'] at h2
    calc α x * f * (α x)⁻¹ = c⁻¹ * (c * (α x * f * (α x)⁻¹)) := by group
      _ = c⁻¹ * c' * (x * f * x⁻¹) := by rw [← h2]; group
  have hcc : c⁻¹ * c' ∈ Subgroup.center X := mul_mem (inv_mem hc) hc'
  have e : x⁻¹ * α x * f * (x⁻¹ * α x)⁻¹ * f⁻¹ = x⁻¹ * (c⁻¹ * c') * x⁻¹⁻¹ := by
    calc x⁻¹ * α x * f * (x⁻¹ * α x)⁻¹ * f⁻¹ = x⁻¹ * (α x * f * (α x)⁻¹) * x * f⁻¹ := by group
      _ = x⁻¹ * (c⁻¹ * c') * x⁻¹⁻¹ := by rw [h1]; group
  rw [e, conj_of_mem_center hcc]
  exact hcc

theorem exists_pow_apply {F : Subgroup X} {α : MulAut X}
    (hαF : ∀ f ∈ F, α f * f⁻¹ ∈ Subgroup.center X) {x : X} (hδ : x⁻¹ * α x ∈ F) (n : ℕ) :
    ∃ z ∈ Subgroup.center X, (α ^ n) x = x * (x⁻¹ * α x) ^ n * z := by
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = x⁻¹ * α x := ⟨_, rfl⟩
  rw [← hδdef] at hδ ⊢
  have hxδ : α x = x * δ := by rw [hδdef]; group
  obtain ⟨c, hc, hcδ⟩ : ∃ c ∈ Subgroup.center X, α δ = c * δ := ⟨_, hαF δ hδ, by group⟩
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz, hzn⟩ := ih
    refine ⟨c ^ n * α z, mul_mem (pow_mem hc n) (map_mem_center α hz), ?_⟩
    have hcomm : Commute c δ := comm_of_mem_center hc δ |>.symm
    have hcomm' : Commute (c ^ n) (δ ^ n) := hcomm.pow_pow n n
    rw [pow_succ', MulAut.mul_apply, hzn, map_mul, map_mul, map_pow, hxδ, hcδ, hcomm.mul_pow,
      hcomm'.eq]
    group

theorem eq_one_of_commFitting [Finite X] (hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    {F : Subgroup X} (hF : F.Normal) (hCF : Subgroup.centralizer (F : Set X) ≤ F)
    (hFodd : Odd (Nat.card F)) {k : Type} [Field k] [Finite k] (hk : 4 ≤ Nat.card k)
    (ψ : X →* SL(2, k)) (hψ : Function.Surjective ψ) (hker : ψ.ker = F)
    {α : MulAut X} {e : ℕ} (hαe : α ^ 2 ^ e = 1)
    (hαF : ∀ f ∈ F, α f * f⁻¹ ∈ Subgroup.center X) : α = 1 := by
  have hZF : Subgroup.center X ≤ F := (Subgroup.center_le_centralizer (F : Set X)).trans hCF
  have hC₁ : centSec F hF ≤ F := by
    have hbot : (centSec F hF).map ψ = ⊥ := by
      have hN : ((centSec F hF).map ψ).Normal := (centSec_normal F hF).map ψ hψ
      refine SL2.eq_bot_of_normal_of_odd hk _ hN ?_
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨Nat.card F, hFodd, ?_⟩
      rw [← map_pow, ← MonoidHom.mem_ker, hker]
      exact hCF (pow_card_mem_centralizer hZF hy)
    intro y hy
    rw [← hker, MonoidHom.mem_ker]
    have : ψ y ∈ (centSec F hF).map ψ := Subgroup.mem_map_of_mem ψ hy
    rwa [hbot, Subgroup.mem_bot] at this
  have hζ : ∀ x : X, x⁻¹ * α x ∈ Subgroup.center X := by
    intro x
    have hδ : x⁻¹ * α x ∈ F := hC₁ (inv_mul_mem_centSec hF hαF x)
    obtain ⟨z, hz, hzx⟩ := exists_pow_apply hαF hδ (2 ^ e)
    rw [hαe, MulAut.one_apply] at hzx
    have h1 : (x⁻¹ * α x) ^ 2 ^ e ∈ Subgroup.center X := by
      have : (x⁻¹ * α x) ^ 2 ^ e = z⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        calc (x⁻¹ * α x) ^ 2 ^ e * z = x⁻¹ * (x * (x⁻¹ * α x) ^ 2 ^ e * z) := by group
          _ = 1 := by rw [← hzx, inv_mul_cancel]
      rw [this]
      exact inv_mem hz
    have h2 : (x⁻¹ * α x) ^ Nat.card F ∈ Subgroup.center X := by
      have h := congrArg Subtype.val (pow_card_eq_one' (G := F) (x := ⟨_, hδ⟩))
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      rw [h]
      exact one_mem _
    have h3 := pow_gcd_mem h1 h2
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hFodd)),
      pow_one] at h3
  let ζ : X →* Subgroup.center X :=
    { toFun := fun x => ⟨x⁻¹ * α x, hζ x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        simp only [Subgroup.coe_mul, map_mul]
        have h := comm_of_mem_center (hζ x) y⁻¹
        calc (x * y)⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = x⁻¹ * α x * y⁻¹ * α y := by rw [h]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by group }
  have hkerζ : ζ.ker = ⊤ := by
    rw [eq_top_iff, ← hperf, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (comm_of_mem_center (ζ g₂).2 _)
  ext x
  have hx : ζ x = 1 := by
    rw [← MonoidHom.mem_ker, hkerζ]
    exact Subgroup.mem_top x
  have h := congrArg Subtype.val hx
  change x⁻¹ * α x = 1 at h
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp h).symm

end AutFit

end CFSG.Quasithin.Vol2.Ch11.SecG
