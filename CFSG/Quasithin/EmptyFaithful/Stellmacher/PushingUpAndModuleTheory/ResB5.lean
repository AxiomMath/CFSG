module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB4
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O2Mod
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA15

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem exists_coord {F N : Subgroup G} [hn : ((⊥ : Subgroup G).subgroupOf N).Normal]
    {Ψ : ↥F →* Perm (Fin 5)} {β : orth.W →* ↥N ⧸ (⊥ : Subgroup G).subgroupOf N}
    (hsd : SecData orth F ⊥ N Ψ β) :
    ∃ γ : orth.W →* G, Function.Injective γ ∧ (∀ w, γ w ∈ N) ∧ (∀ x ∈ N, ∃ w, γ w = x) ∧
      ∀ (k : ↥F) (w : orth.W), γ (orth.act (Ψ k) w) = (k : G) * γ w * (k : G)⁻¹ := by
  have qe : ∀ x y : ↥N, (QuotientGroup.mk x : ↥N ⧸ (⊥ : Subgroup G).subgroupOf N) =
      QuotientGroup.mk y → x = y := by
    intro x y h
    have := (mk_eq_iff_mem.mp h)
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    exact Subtype.ext this.symm
  choose r hr using fun w => QuotientGroup.mk_surjective (β w)
  have hrmul : ∀ w w', r (w * w') = r w * r w' := fun w w' => by
    apply qe
    rw [hr, map_mul, ← hr w, ← hr w', QuotientGroup.mk_mul]
  have hr1 : r 1 = 1 := by
    apply qe
    rw [hr, map_one, QuotientGroup.mk_one]
  let γ : orth.W →* G :=
    { toFun := fun w => ((r w : ↥N) : G)
      map_one' := by simp [hr1]
      map_mul' := fun w w' => by simp [hrmul] }
  refine ⟨γ, fun w w' h => ?_, fun w => (r w).2, fun x hx => ?_, fun k w => ?_⟩
  · have : r w = r w' := Subtype.ext h
    exact hsd.inj (by rw [← hr w, ← hr w', this])
  · obtain ⟨w, hw⟩ := hsd.surj (QuotientGroup.mk (⟨x, hx⟩ : ↥N))
    refine ⟨w, ?_⟩
    have := qe _ _ ((hr w).trans hw)
    exact congrArg Subtype.val this
  · obtain ⟨hkx, h1⟩ := hsd.equiv k w (r w) (hr w).symm
    have := qe _ _ ((hr _).trans h1)
    exact congrArg Subtype.val this

structure OrthFrame (δ μ : Geo H M) where
  Ψ : ↥(stab δ) →* Perm (Fin 5)
  γ : orth.W →* G
  inj : Function.Injective γ
  mem : ∀ w, γ w ∈ OoOf δ
  surj : ∀ x ∈ OoOf δ, ∃ w, γ w = x
  equiv : ∀ (k : ↥(stab δ)) (w : orth.W), γ (orth.act (Ψ k) w) = (k : G) * γ w * (k : G)⁻¹
  ker : ∀ k : ↥(stab δ), Ψ k = 1 ↔ (k : G) ∈ Qv δ
  surjΨ : Function.Surjective Ψ
  syl : ((stab δ ⊓ stab μ).subgroupOf (stab δ)).map Ψ = S5Syl
  mapP : ((Qv μ).subgroupOf (stab δ)).map Ψ = S5That

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem exists_frame (hA : F53Amalgam H M S) (h : ConfR δ μ U) : Nonempty (OrthFrame δ μ) := by
  obtain ⟨c, V₀, -, -, -, -, -, -, -, -, -, -, -, -, horth, -⟩ := h.A3 hA
  have hq := quot_stab_five hA (h.vtype_delta hA)
  have hS := sylow_stab_inf_left hA (h.sig.adj : μ ∈ nbrs δ)
  have hcs : cSecIn (stab δ) ⊥ (OoOf δ) = pCoreOf 2 (stab δ) :=
    IsModelSec.cSecIn_eq_pCoreOf horth hq
  obtain ⟨hnorm, θ, β, hθs, hθk, hsd⟩ := horth
  have := hnorm
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, hsgn⟩ := hsd.exists_normalized hθs hθk hS
  obtain ⟨γ, hinj, hmem, hsurj, hequiv⟩ := exists_coord hsd'
  have hkerΨ : ∀ k : ↥(stab δ), Ψ k = 1 ↔ (k : G) ∈ Qv δ := fun k => by
    rw [← MonoidHom.mem_ker, hkΨ, Subgroup.mem_subgroupOf, hcs]; rfl
  have hPle : Qv μ ≤ stab δ ⊓ stab μ := by
    have := h.sig.P_le_edge hA
    rwa [h.inf_eq] at this
  have hPF : Qv μ ≤ stab δ := hPle.trans inf_le_left
  set PF := (Qv μ).subgroupOf (stab δ) with hPFdef
  have hPS' : PF.map Ψ ≤ S5Syl := by
    rw [← hPS]
    exact Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr (hPle hx))
  have hexp : ∀ y ∈ PF.map Ψ, y ^ 2 = 1 := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 := (h.hmod hA).1 (k : G) (Subgroup.mem_subgroupOf.mp hk)
    rw [← map_pow]
    exact (hkerΨ (k ^ 2)).mpr (by simpa using h1)
  have hcard : Nat.card (PF.map Ψ) = 4 := by
    have h1 := Subgroup.relIndex_ker (K := PF) Ψ
    have hker' : Ψ.ker = (Qv δ).subgroupOf (stab δ) := by
      rw [hkΨ, hcs]; rfl
    rw [hker', hPFdef, Subgroup.relIndex_subgroupOf hPF] at h1
    rw [← h1]
    have h2 := Subgroup.relIndex_mul_card (Qv δ) (Qv μ)
    rw [inf_of_le_left h.hQδ] at h2
    have h3 := h.card_P_R hA
    have h4 := h.card_R_K hA
    have h5 : 0 < Nat.card (Qv δ) := Nat.card_pos
    nlinarith
  obtain ⟨c0, V0, ψ, -, -, hψs, hψker, q, hqP, hqF, hqsign⟩ := h.data hA
  have hψk : ψ.ker = (cSecIn (stab δ) ⊥ (OoOf δ)).subgroupOf (stab δ) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hcs, hψker]; rfl
  have hodd : Ψ ⟨q, hqF⟩ ∉ alternatingGroup (Fin 5) := by
    intro hΨ
    have h1 := (mem_oTwoRes_sup_iff hΨs hkΨ hqF).mpr hΨ
    have h2 := (mem_oTwoRes_sup_iff hψs hψk hqF).mp h1
    rw [Equiv.Perm.mem_alternatingGroup, hqsign] at h2
    exact absurd h2 (by decide)
  have hτ0 : Ψ ⟨q, hqF⟩ ∈ PF.map Ψ := ⟨⟨q, hqF⟩, Subgroup.mem_subgroupOf.mpr hqP, rfl⟩
  have hτ0S : Ψ ⟨q, hqF⟩ ∈ S5SylF := (mem_S5Syl_iff _).mp (hPS' hτ0)
  have hcases : ∀ σ ∈ S5SylF, σ ^ 2 = 1 → Perm.sign σ ≠ 1 → σ = swap 0 2 ∨ σ = swap 1 3 := by
    decide +kernel
  have hsgn1 : Perm.sign (Ψ ⟨q, hqF⟩) ≠ 1 := fun h1 =>
    hodd (Equiv.Perm.mem_alternatingGroup.mpr h1)
  have hτ0' := hcases _ hτ0S (hexp _ hτ0) hsgn1
  have hg : S5g ∈ S5Syl := by rw [mem_S5Syl_iff]; decide +kernel
  have hg' : S5g ∈ ((stab δ ⊓ stab μ).subgroupOf (stab δ)).map Ψ := by rw [hPS]; exact hg
  obtain ⟨s0, hs0, hs0g⟩ := hg'
  have hPnorm : ∀ k : ↥(stab δ), (k : G) ∈ stab δ ⊓ stab μ → ∀ x : ↥(stab δ), x ∈ PF →
      k * x * k⁻¹ ∈ PF := by
    intro k hk x hx
    rw [hPFdef, Subgroup.mem_subgroupOf] at hx ⊢
    have hn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab μ) hk.2
    have key : (k : G) * (x : G) * (k : G)⁻¹ ∈ pCoreOf 2 (stab μ) :=
      (Subgroup.mem_normalizer_iff.mp hn (x : G)).mp hx
    show _ ∈ pCoreOf 2 (stab μ)
    simpa [mul_assoc] using key
  have hsw : swap (0 : Fin 5) 2 ∈ PF.map Ψ ∧ swap (1 : Fin 5) 3 ∈ PF.map Ψ := by
    have hconj : ∀ y ∈ PF.map Ψ, S5g * y * S5g⁻¹ ∈ PF.map Ψ := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨s0 * x * s0⁻¹, hPnorm s0 (Subgroup.mem_subgroupOf.mp hs0) x hx, ?_⟩
      rw [map_mul, map_mul, map_inv, hs0g]
    have e1 : S5g * swap (0 : Fin 5) 2 * S5g⁻¹ = swap 1 3 := by unfold S5g; decide +kernel
    have e2 : S5g * swap (1 : Fin 5) 3 * S5g⁻¹ = swap 0 2 := by unfold S5g; decide +kernel
    rcases hτ0' with e | e
    · refine ⟨e ▸ hτ0, ?_⟩
      have := hconj _ (e ▸ hτ0)
      rwa [e1] at this
    · refine ⟨?_, e ▸ hτ0⟩
      have := hconj _ (e ▸ hτ0)
      rwa [e2] at this
  have hmapP : PF.map Ψ = S5That := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · exact (Subgroup.closure_le _).mpr (by
        rintro x (rfl | rfl)
        exacts [hsw.1, hsw.2])
    · rw [hcard, O2.card_S5That]
  exact ⟨{ Ψ := Ψ
           γ := γ
           inj := hinj
           mem := hmem
           surj := hsurj
           equiv := hequiv
           ker := hkerΨ
           surjΨ := hΨs
           syl := hPS
           mapP := hmapP }⟩

end ConfR

end CFSG.Quasithin.F53
