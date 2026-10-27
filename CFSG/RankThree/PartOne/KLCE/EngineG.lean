module

public import CFSG.RankThree.PartOne.KLCE.Engine
public import CFSG.RankThree.PartOne.KLCE.LayerDatum
public import CFSG.RankThree.PartOne.KLC.LayerData

public noncomputable section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE


section Embedding

variable {τ : Tag} {C : Type} [Group C] {L : Type} [Field L]

@[expose] def psiG (ι : C →* ModGL τ L) (g₀ : ModGL τ L) (c : C) : C →* ModGL τ L :=
  (MulAut.conj g₀⁻¹).toMonoidHom.comp (ι.comp (MulAut.conj c).toMonoidHom)

theorem psiG_apply (ι : C →* ModGL τ L) (g₀ : ModGL τ L) (c y : C) :
    psiG ι g₀ c y = g₀⁻¹ * ι (c * y * c⁻¹) * g₀ := by
  simp [psiG, MulAut.conj_apply]

theorem psiG_injective {ι : C →* ModGL τ L} (hι : Function.Injective ι) (g₀ : ModGL τ L)
    (c : C) : Function.Injective (psiG ι g₀ c) := by
  intro a b hab
  rw [psiG_apply, psiG_apply] at hab
  have h1 := mul_left_cancel (mul_right_cancel hab)
  have h2 := hι h1
  have := congrArg (fun z => c⁻¹ * z * c) h2
  simpa [mul_assoc] using this

theorem psiG_intertwine {ι : C →* ModGL τ L} (F₀ : ModGL τ L →* ModGL τ L) (α₀ : MulAut C)
    (hα₀ : ∀ y, ι (α₀ y) = F₀ (ι y)) {g₀ n₀ : ModGL τ L} (hg₀ : F₀ g₀ = g₀ * n₀) {c : C}
    (hc : α₀ c = c) (y : C) :
    n₀ * F₀ (psiG ι g₀ c y) * n₀⁻¹ = psiG ι g₀ c (α₀ y) := by
  have h1 : α₀ (c * y * c⁻¹) = c * α₀ y * c⁻¹ := by
    rw [map_mul, map_mul, map_inv, hc]
  rw [psiG_apply, psiG_apply, map_mul, map_mul, map_inv, hg₀, ← h1, hα₀]
  group

@[expose] def layerCompG (ι : C →* ModGL τ L) (g₀ : ModGL τ L) (c : C)
    {ι' : Type} (P : ι' → Subgroup (ModGL τ L)) (i : ι') : Subgroup C :=
  (P i).comap (psiG ι g₀ c)

end Embedding

section Structure

variable {τ : Tag} {C : Type} [Group C] [Finite C] {L : Type} [Field L]

theorem layerData_structure_gen (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup τ L) (Φ : ModGL τ L →* ModGL τ L)
    (hιΦ : ∀ y, Φ (ι y) = ι y)
    (hodd : ∀ h ∈ torusGroup τ L, ∃ m : ℕ, Odd m ∧ h ^ m = 1) {p : ℕ} (hp : p.Prime)
    (N g₀ : ModGL τ L) (hg₀C : g₀ ∈ adjointGroup τ L) (hg₀ : Φ g₀ = g₀ * N)
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ x ∈ P, Φ x = x) → ⁅P, P⁆ = P → P ≤ ι.range)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit τ a ∈ twistedTorusOf N Φ →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    {ι' : Type} (P : ι' → Subgroup (ModGL τ L)) (hPfin : ∀ i, Finite (P i))
    (hPq : ∀ i, CFSG.IsQuasisimple (P i)) (hPQ : ∀ i, P i ≤ rootSpan τ L S)
    (hPR : ∀ i, P i ≤ twistedFixedPoints N Φ) (hPadj : ∀ i, P i ≤ adjointGroup τ L)
    (hPnorm : ∀ i, ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints N Φ →
      ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
    (hPcent : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints N Φ →
      (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma N Φ S)
    (hjoin : rootSpan τ L S ⊓ twistedFixedPoints N Φ ≤ ⨆ i, P i)
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ P i, ∀ v ∈ P j, u * v = v * u)
    {x : C} (hx : orderOf x = p) (c : C)
    (hc : c * x * c⁻¹ ∈ subtorusImage ι g₀ (subtorusSigma N Φ S))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g₀⁻¹ * ι (c * x * c⁻¹) * g₀ →
      rootCharKernel a ⊆ S) :
    (∀ i, P i ≤ (psiG ι g₀ c).range) ∧
      (∀ i, CFSG.RankThree.PartOne.IsComponentOf (Subgroup.centralizer ({x} : Set C))
        (layerCompG ι g₀ c P i)) ∧
      Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set C) ⊓
        Subgroup.centralizer ((⨆ i, layerCompG ι g₀ c P i : Subgroup C) : Set C)) ∧
      ((⨆ i, layerCompG ι g₀ c P i : Subgroup C).subgroupOf
        (Subgroup.centralizer ({x} : Set C))).Normal ∧
      Odd ((⨆ i, layerCompG ι g₀ c P i : Subgroup C).subgroupOf
        (Subgroup.centralizer ({x} : Set C))).index := by
  classical
  have hψtinj : Function.Injective (psiG ι g₀ c) := psiG_injective hι g₀ c
  obtain ⟨ψ, -, hψ, hψHQ, hψR, -, hPψ, -⟩ := sigma_embedding_data_of_stab ι hι hιC Φ hιΦ N g₀
    hg₀C hg₀ hperf hp hstab hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c hc hkerZ
  have hψt_eq : ∀ y : Subgroup.centralizer ({x} : Set C), psiG ι g₀ c y = ψ y := fun y => by
    rw [hψ y, psiG_apply]
  have hψt_mem : ∀ y ∈ Subgroup.centralizer ({x} : Set C),
      psiG ι g₀ c y ∈ torusGroup τ L ⊔ rootSpan τ L S ∧
      N * Φ (psiG ι g₀ c y) * N⁻¹ = psiG ι g₀ c y := fun y hy => by
    have h := hψt_eq ⟨y, hy⟩
    exact ⟨h ▸ hψHQ ⟨y, hy⟩, h ▸ hψR ⟨y, hy⟩⟩
  have hPrange : ∀ i, P i ≤ (psiG ι g₀ c).range := fun i u hu => by
    obtain ⟨y, hy⟩ := hPψ i hu
    exact ⟨y, (hψt_eq y).trans hy⟩
  have hmap : ∀ i, (layerCompG ι g₀ c P i).map (psiG ι g₀ c) = P i := fun i => by
    unfold layerCompG
    rw [Subgroup.map_comap_eq, inf_eq_right.2 (hPrange i)]
  have hz : psiG ι g₀ c x ∈ subtorusSigma N Φ S := by
    rw [psiG_apply]
    exact (mem_subtorusImage_iff ι g₀ _ (c * x * c⁻¹)).1 hc
  have hQX : ∀ i, layerCompG ι g₀ c P i ≤ Subgroup.centralizer ({x} : Set C) :=
    fun i y hy => by
    have h1 : psiG ι g₀ c y ∈ P i := hy
    have h2 := Subgroup.mem_centralizer_iff.1 hz.2 _ (hPQ i h1)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    apply hψtinj
    rw [map_mul, map_mul]
    exact h2
  have hJQ : (⨆ i, layerCompG ι g₀ c P i : Subgroup C) =
      (⨆ i, P i).comap (psiG ι g₀ c) := by
    have h1 : (⨆ i, layerCompG ι g₀ c P i : Subgroup C).map (psiG ι g₀ c) = ⨆ i, P i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr hmap
    rw [← h1]
    exact (Subgroup.comap_map_eq_self_of_injective hψtinj _).symm
  have hmemJQ : ∀ y, y ∈ (⨆ i, layerCompG ι g₀ c P i : Subgroup C) ↔
      psiG ι g₀ c y ∈ ⨆ i, P i := fun y => by
    rw [hJQ]
    rfl
  have hnormP : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints N Φ →
      ∀ v ∈ ⨆ i, P i, y * v * y⁻¹ ∈ ⨆ i, P i := by
    intro y hy hyR v hv
    have hle : (⨆ i, P i) ≤ (⨆ i, P i).comap (MulAut.conj y).toMonoidHom :=
      iSup_le fun i u hu => by
        change y * u * y⁻¹ ∈ ⨆ i, P i
        exact le_iSup P i (hPnorm i y hy hyR u hu)
    exact hle hv
  have hnormal : ((⨆ i, layerCompG ι g₀ c P i : Subgroup C).subgroupOf
      (Subgroup.centralizer ({x} : Set C))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hmemJQ] at hn ⊢
    have hg := hψt_mem (g : C) g.2
    have h := hnormP _ hg.1 hg.2 _ hn
    change psiG ι g₀ c ((g : C) * (n : C) * (g : C)⁻¹) ∈ _
    rw [map_mul, map_mul, map_inv]
    exact h
  have hodd' : Odd ((⨆ i, layerCompG ι g₀ c P i : Subgroup C).subgroupOf
      (Subgroup.centralizer ({x} : Set C))).index := by
    have : Finite ↥(Subgroup.centralizer ({x} : Set C)) := inferInstance
    refine odd_index_of_sq_mem _ (fun g hg => ?_)
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    have hg2 : psiG ι g₀ c ((g : C) ^ 2) ∈ ⨆ i, P i :=
      (hmemJQ _).1 (by simpa using hg)
    rw [map_pow] at hg2
    obtain ⟨hHQ, hR⟩ := hψt_mem (g : C) g.2
    obtain ⟨t, ht, q, hq, hu⟩ := exists_mul_of_mem_torus_sup_rootSpan hS hHQ
    have hq2 : (psiG ι g₀ c (g : C)) ^ 2 ∈ rootSpan τ L S :=
      (iSup_le hPQ : (⨆ i, P i) ≤ rootSpan τ L S) hg2
    rw [hu, pow_two] at hq2
    have h1 : t * q * t ∈ rootSpan τ L S := by
      have := mul_mem hq2 (inv_mem hq)
      simpa [mul_assoc] using this
    have hnorm : t ∈ Subgroup.normalizer (rootSpan τ L S : Set (ModGL τ L)) :=
      KE.torusGroup_le_normalizer_rootSpan hS ht
    have h2 : t * q * t⁻¹ ∈ rootSpan τ L S := (Subgroup.mem_normalizer_iff.1 hnorm q).1 hq
    have ht2 : t ^ 2 ∈ rootSpan τ L S := by
      have : t ^ 2 = (t * q * t⁻¹)⁻¹ * (t * q * t) := by rw [pow_two]; group
      rw [this]
      exact mul_mem (inv_mem h2) h1
    obtain ⟨m, hm, htm⟩ := hodd t ht
    obtain ⟨k, hk⟩ := hm
    have e1 : t ^ (2 * k + 1) = 1 := by rw [← hk]; exact htm
    have htQ : t ∈ rootSpan τ L S := by
      have : t = (t ^ 2) ^ (k + 1) := by
        calc t = t ^ (2 * k + 1) * t := by rw [e1, one_mul]
          _ = t ^ (2 * k + 1 + 1) := (pow_succ _ _).symm
          _ = (t ^ 2) ^ (k + 1) := by rw [← pow_mul]; ring_nf
      rw [this]
      exact pow_mem ht2 _
    have huQ : psiG ι g₀ c (g : C) ∈ rootSpan τ L S := by
      rw [hu]
      exact mul_mem htQ hq
    exact (hmemJQ _).2 (hjoin ⟨huQ, hR⟩)
  have hequiv : ∀ i, ↥(layerCompG ι g₀ c P i) ≃* ↥(P i) := fun i =>
    (Subgroup.equivMapOfInjective _ (psiG ι g₀ c) hψtinj).trans
      (MulEquiv.subgroupCongr (hmap i))
  have hquasi : ∀ i, CFSG.IsQuasisimple ↥(layerCompG ι g₀ c P i) := fun i =>
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (hequiv i).symm (hPq i)
  have hcommQ : ∀ i j, i ≠ j → ∀ y ∈ layerCompG ι g₀ c P i, ∀ y' ∈ layerCompG ι g₀ c P j,
      y * y' = y' * y := fun i j hij y hy y' hy' => by
    apply hψtinj
    rw [map_mul, map_mul]
    exact hcomm i j hij _ hy _ hy'
  have hJle : ∀ i, (⨆ j, layerCompG ι g₀ c P j : Subgroup C) ≤
      Subgroup.normalizer ((layerCompG ι g₀ c P i : Subgroup C) : Set C) := fun i => by
    refine iSup_le fun j => ?_
    by_cases hij : j = i
    · subst hij
      exact Subgroup.le_normalizer
    · intro y hy
      refine Subgroup.mem_normalizer_iff.2 fun u => ?_
      have hconj : ∀ u ∈ layerCompG ι g₀ c P i, y * u * y⁻¹ = u := fun u hu => by
        rw [← hcommQ i j (Ne.symm hij) u hu y hy]
        group
      constructor
      · intro hu
        rw [hconj u hu]
        exact hu
      · intro hu
        have e := hconj _ hu
        have e2 : y * u * y⁻¹ = u := by
          have := congrArg (fun z => y⁻¹ * z * y) e
          simpa [mul_assoc] using this
        rw [e2] at hu
        exact hu
  have hsub : ∀ i, ((layerCompG ι g₀ c P i).subgroupOf
      (Subgroup.centralizer ({x} : Set C))).IsSubnormal := fun i => by
    refine Subgroup.IsSubnormal.step _
      ((⨆ j, layerCompG ι g₀ c P j : Subgroup C).subgroupOf
        (Subgroup.centralizer ({x} : Set C))) ?_ hnormal.isSubnormal ?_
    · intro a ha
      exact Subgroup.mem_subgroupOf.2
        (le_iSup (layerCompG ι g₀ c P) i (Subgroup.mem_subgroupOf.1 ha))
    · refine ⟨fun b hb a => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hb ⊢
      have ha : (a : Subgroup.centralizer ({x} : Set C)) ∈ _ := a.2
      rw [Subgroup.mem_subgroupOf] at ha
      have h := (Subgroup.mem_normalizer_iff.1 (hJle i ha) _).1 hb
      simpa using h
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set C) ⊓
      Subgroup.centralizer ((⨆ i, layerCompG ι g₀ c P i : Subgroup C) : Set C)) := by
    have hmemT : ∀ y ∈ Subgroup.centralizer ({x} : Set C) ⊓
        Subgroup.centralizer ((⨆ i, layerCompG ι g₀ c P i : Subgroup C) : Set C),
        psiG ι g₀ c y ∈ torusGroup τ L := by
      intro y hy
      obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨hHQ, hR⟩ := hψt_mem y hyX
      have := hPcent _ hHQ hR (fun i u hu => by
        obtain ⟨w, hw⟩ := hPrange i hu
        have hwQ : w ∈ layerCompG ι g₀ c P i := by
          show psiG ι g₀ c w ∈ P i
          rw [hw]
          exact hu
        have hwJ : w ∈ (⨆ i, layerCompG ι g₀ c P i : Subgroup C) :=
          le_iSup (layerCompG ι g₀ c P) i hwQ
        have h := Subgroup.mem_centralizer_iff.1 hyC w hwJ
        have h2 : psiG ι g₀ c (w * y) = psiG ι g₀ c (y * w) := by rw [h]
        rw [map_mul, map_mul, hw] at h2
        exact h2.symm)
      exact (mem_twistedTorusOf.1 (subtorusSigma_le_twistedTorusOf _ _ _ this)).1
    refine Group.isSolvable_of_comm (fun a b => ?_)
    apply Subtype.ext
    apply hψtinj
    have ha := hmemT a a.2
    have hb := hmemT b b.2
    change psiG ι g₀ c ((a : C) * b) = psiG ι g₀ c ((b : C) * a)
    rw [map_mul, map_mul]
    exact KE.torusGroup_comm ha hb
  exact ⟨hPrange, fun i => ⟨hQX i, hquasi i, hsub i⟩, hsolv, hnormal, hodd'⟩

end Structure

section Descent

variable {τ : Tag} {C : Type} [Group C] [Finite C] {L : Type} [Field L]

theorem lieLayerData_of_descent (ι : C →* ModGL τ L) (hι : Function.Injective ι)
    (hιC : ∀ y, ι y ∈ adjointGroup τ L) (F₀ Φ : ModGL τ L →* ModGL τ L) (α₀ : MulAut C)
    (hα₀ : ∀ y, ι (α₀ y) = F₀ (ι y)) {p : ℕ} (hp : p.Prime) (hα₀p : α₀ ^ p = 1)
    (hιΦ : ∀ y, Φ (ι y) = ι y)
    (hodd : ∀ h ∈ torusGroup τ L, ∃ m : ℕ, Odd m ∧ h ^ m = 1)
    (n₀ N g₀ : ModGL τ L) (hg₀C : g₀ ∈ adjointGroup τ L) (hg₀F : F₀ g₀ = g₀ * n₀)
    (hg₀ : Φ g₀ = g₀ * N)
    (hperf : ∀ P : Subgroup (ModGL τ L), Finite P → P ≤ adjointGroup τ L →
      (∀ x ∈ P, Φ x = x) → ⁅P, P⁆ = P → P ≤ ι.range)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
      rootDiagUnit τ a ∈ twistedTorusOf N Φ →
      rootCharStabilizer a ⊆ (Subgroup.closure
        {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ)))
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) (hSn : ∀ α ∈ S, -α ∈ S)
    {ι' : Type} (P : ι' → Subgroup (ModGL τ L)) (hne : Nonempty ι')
    (hPfin : ∀ i, Finite (P i))
    (hPq : ∀ i, CFSG.IsQuasisimple (P i)) (hPQ : ∀ i, P i ≤ rootSpan τ L S)
    (hPR : ∀ i, P i ≤ twistedFixedPoints N Φ) (hPadj : ∀ i, P i ≤ adjointGroup τ L)
    (hPnorm : ∀ i, ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints N Φ →
      ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
    (hPcent : ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints N Φ →
      (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma N Φ S)
    (hjoin : rootSpan τ L S ⊓ twistedFixedPoints N Φ ≤ ⨆ i, P i)
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ P i, ∀ v ∈ P j, u * v = v * u)
    (hLD : ∀ i, LayerDatum p (fun u => n₀ * F₀ u * n₀⁻¹) (P i))
    {x : C} (hx : orderOf x = p) (hpr : CFSG.pRank p C = 1) (c : C) (hcα : α₀ c = c)
    (hc : c * x * c⁻¹ ∈ subtorusImage ι g₀ (subtorusSigma N Φ S))
    (hkerZ : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a = g₀⁻¹ * ι (c * x * c⁻¹) * g₀ →
      rootCharKernel a ⊆ S) :
    KLC.LieLayerData p α₀ (Subgroup.centralizer ({x} : Set C)) := by
  obtain ⟨hPrange, hcomp, hsolv, hnormal, hoddi⟩ := layerData_structure_gen ι hι hιC Φ hιΦ hodd hp
    N g₀ hg₀C hg₀ hperf hstab hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hjoin hcomm hx c hc
    hkerZ
  refine ⟨ι', fun i => layerCompG ι g₀ c P i, hne, hcomp, hsolv, hnormal, hoddi,
    fun i hstabQ => ?_⟩
  exact hLD i C (psiG ι g₀ c) (psiG_injective hι g₀ c) (hPrange i) α₀ hα₀p
    (fun g => (psiG_intertwine F₀ α₀ hα₀ hg₀F hcα g).symm) x hx hpr
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.1 ((hcomp i).1 hy)) hstabQ

end Descent

end CFSG.RankThree.PartOne.KLCE
