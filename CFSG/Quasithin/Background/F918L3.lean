module

public import CFSG.Quasithin.Background.F918J7
public import CFSG.Quasithin.Background.F918L1
public import CFSG.Quasithin.Background.F918L2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

theorem d3A38_of_a38 (h38 : A38ForSQTKCat) : D3A38 := by
  intro W _ _ M Mp T L V std t ht htn hMp
  have hD := std.hyp
  have hTM : T ≤ M := hD.sylow.1
  have hLM : L ≤ M := le_of_mem_cComp hD.comp
  have hO2 : CFSG.pCore 2 ↥M = ⊥ := by
    have h := D31.pCoreOf_eq_bot hD
    unfold pCoreOf at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h
  have hLc : L.subgroupOf M ∈ cComp (⊤ : Subgroup ↥M) := subgroupOf_mem_cComp hD.comp
  obtain ⟨Shat, _, φ, hφ, hSQ, Lhat, hLhat, hmap⟩ := exists_sqtk_cover hD.qsqtk hO2 hLc
  have hnn : ¬ Lhat.Normal := by
    intro hN
    have hLN : (L.subgroupOf M).Normal := hmap ▸ hN.map φ hφ
    have key : ∀ s ∈ M, ∀ x ∈ L, s * x * s⁻¹ ∈ L := fun s hs x hx => by
      have := hLN.conj_mem ⟨x, hLM hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨s, hs⟩
      exact Subgroup.mem_subgroupOf.mp this
    apply htn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => key t (hTM ht) x hx
    · intro h
      have := key t⁻¹ (M.inv_mem (hTM ht)) _ h
      simpa [mul_assoc] using this
  rcases (h38 Shat hSQ Lhat hLhat).1 with hN | ⟨hAT, -⟩
  · exact absurd hN hnn
  ·
    have hsimple : IsSimpleGroup ↥Lhat :=
      CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hAT
    have hnt : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hD.quasi
    let ψ : ↥Lhat →* ↥M := φ.comp Lhat.subtype
    have hrange : ψ.range = L.subgroupOf M := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact hmap
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases hsimple.eq_bot_or_eq_top_of_normal ψ.ker with h | h
      · exact h
      · exfalso
        have h1 : ψ.range = ⊥ := by
          rw [eq_bot_iff]
          rintro _ ⟨x, rfl⟩
          exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
        rw [hrange] at h1
        obtain ⟨x, hx1⟩ := exists_ne (1 : ↥L)
        have hx : (⟨(x : MulAut W), hLM x.2⟩ : ↥M) ∈ L.subgroupOf M := Subgroup.mem_subgroupOf.mpr x.2
        rw [h1, Subgroup.mem_bot] at hx
        have hx' := congrArg Subtype.val hx
        exact hx1 (Subtype.ext (by simpa using hx'))
    let e : ↥Lhat ≃* ↥L :=
      (MonoidHom.ofInjective hinj).trans
        ((MulEquiv.subgroupCongr hrange).trans (Subgroup.subgroupOfEquivOfLe hLM))
    exact a38Types_congr e hAT

end CFSG.Quasithin
