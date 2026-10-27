module

public import CFSG.Quasithin.EmptyFaithful.S153G93Split
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

namespace S153G93D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

@[expose] def A38TypesSimple : Prop := ∀ (X : Type) [Group X], A38Types X → IsSimpleGroup X

structure TwoStruct {Q : Type} [Group Q] (K N N' : Subgroup Q) (g : Q) : Prop where
  conj_eq : N' = N.map (MulAut.conj g).toMonoidHom
  ne : N ≠ N'
  sup : K = N ⊔ N'
  comp₁ : CFSG.IsComponent N
  comp₂ : CFSG.IsComponent N'
  a38 : A38Types ↥N
  comm : ∀ x ∈ N, ∀ y ∈ N', x * y = y * x
  allcomp : ∀ M : Subgroup Q, CFSG.IsComponent M → M ≤ K → M = N ∨ M = N'

section Center

variable {Q : Type} [Group Q] {K : Subgroup Q}

theorem inf_centralizer_eq_bot (hKn : K.Normal)
    (hmin : ∀ M : Subgroup Q, M.Normal → M ≤ K → M = ⊥ ∨ M = K)
    (hnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) :
    K ⊓ Subgroup.centralizer (K : Set Q) = ⊥ := by
  have hnorm : (K ⊓ Subgroup.centralizer (K : Set Q)).Normal := by
    refine ⟨fun n hn q => ?_⟩
    have hn' : n ∈ K ∧ n ∈ Subgroup.centralizer (K : Set Q) := hn
    obtain ⟨hnK, hnc'⟩ := hn'
    refine ⟨hKn.conj_mem n hnK q, ?_⟩
    show q * n * q⁻¹ ∈ Subgroup.centralizer (K : Set Q)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : q⁻¹ * y * q ∈ K := by
      have := hKn.conj_mem y hy q⁻¹
      simpa using this
    have h1 : n * (q⁻¹ * y * q) = (q⁻¹ * y * q) * n :=
      (Subgroup.mem_centralizer_iff.mp hnc' _ hy').symm
    calc y * (q * n * q⁻¹) = q * ((q⁻¹ * y * q) * n) * q⁻¹ := by group
      _ = q * (n * (q⁻¹ * y * q)) * q⁻¹ := by rw [h1]
      _ = q * n * q⁻¹ * y := by group
  rcases hmin _ hnorm inf_le_left with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    have hxK : x ∈ K ⊓ Subgroup.centralizer (K : Set Q) := by rw [h]; exact hx
    exact hxy (Subgroup.mem_centralizer_iff.mp hxK.2 y hy).symm

end Center

section Structure

theorem map_conj_eq_self_of_normal {Q : Type} [Group Q] {N : Subgroup Q} (hN : N.Normal) (g : Q) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hN.conj_mem x hx g
  · intro y hy
    refine ⟨g⁻¹ * y * g, ?_, by show g * (g⁻¹ * y * g) * g⁻¹ = y; group⟩
    have := hN.conj_mem y hy g⁻¹
    simpa using this

theorem exists_twoStruct (h38 : A38ForSQTKCat) (hS : A38TypesSimple) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuotientOfSQTKTC Q) (hO2 : CFSG.pCore 2 Q = ⊥) {K : Subgroup Q} (hKn : K.Normal)
    (hK1 : K ≠ ⊥) (hmin : ∀ M : Subgroup Q, M.Normal → M ≤ K → M = ⊥ ∨ M = K)
    (hnc : ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x) :
    CFSG.IsComponent K ∨ ∃ (N N' : Subgroup Q) (g : Q), TwoStruct K N N' g := by
  obtain ⟨N, hNc, hNK, hcase⟩ := S153G93.exists_split_of_a38 h38 hQ hO2 hKn hK1 hmin hnc
  rcases hcase with hKN | ⟨g, hne, hgc, hsup⟩
  · left
    rw [hKN]
    exact hNc
  · right
    refine ⟨N, N.map (MulAut.conj g).toMonoidHom, g, ?_⟩
    have hZ := inf_centralizer_eq_bot hKn hmin hnc
    have hnn : ¬ N.Normal := fun h => hne (map_conj_eq_self_of_normal h g)
    have hNcomp : N ∈ cComp (⊤ : Subgroup Q) := mem_cComp_top_of_isComponent hNc
    obtain ⟨Shat, _, φ, hφ, hSQ, Lhat, hLhat, hmap⟩ := exists_sqtk_cover hQ hO2 hNcomp
    have ha38 : A38Types ↥N := by
      rcases (h38 Shat hSQ Lhat hLhat).1 with hN | ⟨hAT, -⟩
      · exact absurd (hmap ▸ hN.map φ hφ) hnn
      · have hsimple : IsSimpleGroup ↥Lhat := hS _ hAT
        have hnt : Nontrivial ↥N := CFSG.LocalCores.isQuasisimple_nontrivial hNc.1
        let ψ : ↥Lhat →* Q := φ.comp Lhat.subtype
        have hrange : ψ.range = N := by
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
            exact (Subgroup.nontrivial_iff_ne_bot N).mp hnt h1
        let e : ↥Lhat ≃* ↥N :=
          (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
        exact a38Types_congr e hAT
    refine ⟨rfl, fun h => hne h.symm, hsup, hNc, hgc, ha38, ?_, ?_⟩
    · intro x hx y hy
      rcases CFSG.LocalCores.distinct_components_commute hNc hgc with h | h
      · exact absurd h.symm hne
      · have hmem : ⁅x, y⁆ ∈ ⁅N, N.map (MulAut.conj g).toMonoidHom⁆ :=
          Subgroup.commutator_mem_commutator hx hy
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
        exact hmem
    · intro M hM hMK
      by_contra hcon
      push Not at hcon
      have hMN : ⁅M, N⁆ = ⊥ := by
        rcases CFSG.LocalCores.distinct_components_commute hM hNc with h | h
        · exact absurd h hcon.1
        · exact h
      have hMN' : ⁅M, N.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
        rcases CFSG.LocalCores.distinct_components_commute hM hgc with h | h
        · exact absurd h hcon.2
        · exact h
      have hcent : M ≤ Subgroup.centralizer (K : Set Q) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : y ∈ Subgroup.centralizer ({z} : Set Q) := by
          have hN1 : N ≤ Subgroup.centralizer ({z} : Set Q) := by
            intro n hn
            rw [Subgroup.mem_centralizer_singleton_iff]
            have hmem : ⁅n, z⁆ ∈ ⁅N, M⁆ := Subgroup.commutator_mem_commutator hn hz
            rw [Subgroup.commutator_comm, hMN, Subgroup.mem_bot,
              commutatorElement_eq_one_iff_mul_comm] at hmem
            exact hmem
          have hN2 : N.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({z} : Set Q) := by
            intro n hn
            rw [Subgroup.mem_centralizer_singleton_iff]
            have hmem : ⁅n, z⁆ ∈ ⁅N.map (MulAut.conj g).toMonoidHom, M⁆ :=
              Subgroup.commutator_mem_commutator hn hz
            rw [Subgroup.commutator_comm, hMN', Subgroup.mem_bot,
              commutatorElement_eq_one_iff_mul_comm] at hmem
            exact hmem
          rw [hsup] at hy
          exact (sup_le hN1 hN2) hy
        rw [Subgroup.mem_centralizer_singleton_iff] at hy'
        exact hy'
      have hbot : M = ⊥ := by
        rw [eq_bot_iff, ← hZ]
        exact le_inf hMK hcent
      have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hM.1
      exact (Subgroup.nontrivial_iff_ne_bot M).mp hnt hbot

end Structure

section Swap

variable {Q : Type} [Group Q]

theorem map_conj_mul (N : Subgroup Q) (x y : Q) :
    N.map (MulAut.conj (x * y)).toMonoidHom =
      (N.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

theorem map_conj_eq_iff_mem_normalizer (N : Subgroup Q) (x : Q) :
    N.map (MulAut.conj x).toMonoidHom = N ↔ x ∈ Subgroup.normalizer (N : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    constructor
    · intro hy
      rw [← h]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← h] at hy
      obtain ⟨n, hn, hny⟩ := hy
      have : n = y := by
        have h2 : x * n * x⁻¹ = x * y * x⁻¹ := hny
        simpa using h2
      rw [← this]
      exact hn
  · intro h
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact (h n).1 hn
    · intro hy
      refine ⟨x⁻¹ * y * x, ?_, by show x * (x⁻¹ * y * x) * x⁻¹ = y; group⟩
      have := (h (x⁻¹ * y * x)).2 (by
        have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
        rw [e]
        exact hy)
      exact this

theorem TwoStruct.conj_cases {K N N' : Subgroup Q} {g : Q} (hK : TwoStruct K N N' g)
    (hKn : K.Normal) (x : Q) :
    N.map (MulAut.conj x).toMonoidHom = N ∨ N.map (MulAut.conj x).toMonoidHom = N' := by
  refine hK.allcomp _ (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hK.comp₁) ?_
  rintro _ ⟨n, hn, rfl⟩
  exact hKn.conj_mem n (hK.sup ▸ (le_sup_left : N ≤ N ⊔ N') hn) x

theorem TwoStruct.conj_cases' {K N N' : Subgroup Q} {g : Q} (hK : TwoStruct K N N' g)
    (hKn : K.Normal) (x : Q) :
    N'.map (MulAut.conj x).toMonoidHom = N ∨ N'.map (MulAut.conj x).toMonoidHom = N' := by
  refine hK.allcomp _ (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hK.comp₂) ?_
  rintro _ ⟨n, hn, rfl⟩
  exact hKn.conj_mem n (hK.sup ▸ (le_sup_right : N' ≤ N ⊔ N') hn) x

theorem TwoStruct.index_normalizer {K N N' : Subgroup Q} {g : Q} (hK : TwoStruct K N N' g)
    (hKn : K.Normal) : (Subgroup.normalizer (N : Set Q)).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨g, fun b => ?_⟩
  have hbg : N.map (MulAut.conj (b * g)).toMonoidHom = N'.map (MulAut.conj b).toMonoidHom := by
    rw [map_conj_mul, ← hK.conj_eq]
  have hne : N.map (MulAut.conj b).toMonoidHom ≠ N'.map (MulAut.conj b).toMonoidHom := fun h =>
    hK.ne (Subgroup.map_injective (MulAut.conj b).injective h)
  rw [← map_conj_eq_iff_mem_normalizer, ← map_conj_eq_iff_mem_normalizer, hbg]
  rcases hK.conj_cases hKn b with h1 | h1
  · rcases hK.conj_cases' hKn b with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · refine Or.inr ⟨h1, ?_⟩
      rw [h2]
      exact hK.ne.symm
  · rcases hK.conj_cases' hKn b with h2 | h2
    · refine Or.inl ⟨h2, ?_⟩
      rw [h1]
      exact hK.ne.symm
    · exact absurd (h1.trans h2.symm) hne

theorem exists_swap_of_sylow {K N N' : Subgroup Q} {g : Q} (hK : TwoStruct K N N' g)
    (hKn : K.Normal) {T : Subgroup Q} (hT : IsSylowTwoOf T ⊤) :
    ∃ t ∈ T, N.map (MulAut.conj t).toMonoidHom = N' := by
  by_contra hcon
  push Not at hcon
  have hTP : T ≤ Subgroup.normalizer (N : Set Q) := fun t ht => by
    rw [← map_conj_eq_iff_mem_normalizer]
    rcases hK.conj_cases hKn t with h | h
    · exact h
    · exact absurd h (hcon t ht)
  have hdvd := Subgroup.index_dvd_of_le hTP
  rw [hK.index_normalizer hKn] at hdvd
  have h2 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
  exact hT.2.2 (h2 ▸ hdvd)

end Swap

end S153G93D

end CFSG.Quasithin
