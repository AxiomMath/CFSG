module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveChiefA
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Defs
public import CFSG.GroupTheory.CyclicDiagonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isKGroup_map_of_injective {G H : Type} [Group G] [Group H]
    {L : Subgroup G} (hL : CFSG.Open.IsKGroup ↥L) (ψ : G →* H)
    (hψ : Function.Injective (ψ.comp L.subtype)) :
    CFSG.Open.IsKGroup ↥(L.map ψ) := by
  let f : ↥L →* ↥(L.map ψ) := ψ.subgroupMap L
  have hf : Function.Injective f := by
    intro x y hxy
    apply hψ
    simpa [f, MonoidHom.subgroupMap_apply_coe] using congrArg Subtype.val hxy
  have hsurj : Function.Surjective f := MonoidHom.subgroupMap_surjective ψ L
  let e : ↥L ≃* ↥(L.map ψ) := MulEquiv.ofBijective f ⟨hf, hsurj⟩
  exact CFSG.Open.IsKGroup.of_surjective hL e.toMonoidHom e.surjective

namespace ChiefSetup

variable {D : Data G} {V₀ V : Subgroup G} (s : ChiefSetup D V₀ V)

section Data


section Diagonal

variable {r : ℕ} {S : Fin r → Subgroup s.Q} (hFac : IsFactorization s.Rbar S) {i₀ : Fin r}

theorem conjugatePower_eq_factor {a : s.Q} (k : ℕ) :
    CFSG.GroupTheory.conjugatePower a (S i₀) k = S ((hFac.actHom a ^ k) i₀) := by
  change (S i₀).map (MulAut.conj (a ^ k)).toMonoidHom = S ((hFac.actHom a ^ k) i₀)
  rw [hFac.S_actHom_pow]

theorem actHom_pow_injective {a : s.Q} {ℓ : ℕ} (hℓ : ℓ.Prime) (ha : a ^ ℓ = 1)
    (ha1 : a ≠ 1)
    (hN : a ∉ Subgroup.normalizer ((S i₀ : Subgroup s.Q) : Set s.Q)) :
    ∀ i j : Fin ℓ,
      (hFac.actHom a ^ (i : ℕ)) i₀ = (hFac.actHom a ^ (j : ℕ)) i₀ → i = j := by
  intro i j hij
  by_contra hne
  have hvalne : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hvalne with hlt | hlt
  · have hd_fix : (hFac.actHom a ^ ((j : ℕ) - (i : ℕ))) i₀ = i₀ := by
      have hji : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)) :=
        (Nat.add_sub_cancel' hlt.le).symm
      have hpow : hFac.actHom a ^ (j : ℕ) =
          hFac.actHom a ^ (i : ℕ) * hFac.actHom a ^ ((j : ℕ) - (i : ℕ)) := by
        rw [← pow_add, ← hji]
      have h1 : ((hFac.actHom a ^ (i : ℕ))⁻¹ * hFac.actHom a ^ (j : ℕ)) =
          hFac.actHom a ^ ((j : ℕ) - (i : ℕ)) := by
        rw [hpow, ← mul_assoc, inv_mul_cancel, one_mul]
      have h2 : ((hFac.actHom a ^ (i : ℕ))⁻¹ * hFac.actHom a ^ (j : ℕ)) i₀ = i₀ := by
        rw [Equiv.Perm.mul_apply, ← hij]
        simp
      rwa [h1] at h2
    have hgm : hFac.actHom (a ^ ((j : ℕ) - (i : ℕ))) i₀ = i₀ := by
      rw [map_pow]
      exact hd_fix
    have hNd : a ^ ((j : ℕ) - (i : ℕ)) ∈
        Subgroup.normalizer ((S i₀ : Subgroup s.Q) : Set s.Q) :=
      hFac.actHom_eq_iff.mp hgm
    exact hN (CFSG.LocalAnalysis.RankThreeTheoremC.mem_normalizer_of_pow_mem hℓ ha
        (Nat.coprime_of_lt_prime (by omega) (by omega) hℓ).symm hNd)
  · have hd_fix : (hFac.actHom a ^ ((i : ℕ) - (j : ℕ))) i₀ = i₀ := by
      have hij' : (hFac.actHom a ^ (j : ℕ)) i₀ = (hFac.actHom a ^ (i : ℕ)) i₀ := hij.symm
      have hji : (i : ℕ) = (j : ℕ) + ((i : ℕ) - (j : ℕ)) :=
        (Nat.add_sub_cancel' hlt.le).symm
      have hpow : hFac.actHom a ^ (i : ℕ) =
          hFac.actHom a ^ (j : ℕ) * hFac.actHom a ^ ((i : ℕ) - (j : ℕ)) := by
        rw [← pow_add, ← hji]
      have h1 : ((hFac.actHom a ^ (j : ℕ))⁻¹ * hFac.actHom a ^ (i : ℕ)) =
          hFac.actHom a ^ ((i : ℕ) - (j : ℕ)) := by
        rw [hpow, ← mul_assoc, inv_mul_cancel, one_mul]
      have h2 : ((hFac.actHom a ^ (j : ℕ))⁻¹ * hFac.actHom a ^ (i : ℕ)) i₀ = i₀ := by
        rw [Equiv.Perm.mul_apply, ← hij']
        simp
      rwa [h1] at h2
    have hgm : hFac.actHom (a ^ ((i : ℕ) - (j : ℕ))) i₀ = i₀ := by
      rw [map_pow]
      exact hd_fix
    have hNd : a ^ ((i : ℕ) - (j : ℕ)) ∈
        Subgroup.normalizer ((S i₀ : Subgroup s.Q) : Set s.Q) :=
      hFac.actHom_eq_iff.mp hgm
    exact hN (CFSG.LocalAnalysis.RankThreeTheoremC.mem_normalizer_of_pow_mem hℓ ha
        (Nat.coprime_of_lt_prime (by omega) (by omega) hℓ).symm hNd)

theorem conjugatesCommute (hFac : IsFactorization s.Rbar S) {a : s.Q} {ℓ : ℕ}
    (hℓ : ℓ.Prime) (ha : a ^ ℓ = 1)
    (ha1 : a ≠ 1)
    (hN : a ∉ Subgroup.normalizer ((S i₀ : Subgroup s.Q) : Set s.Q)) :
    CFSG.GroupTheory.ConjugatesCommute a (S i₀) ℓ := by
  intro i j hij x hx y hy
  rw [conjugatePower_eq_factor s hFac i] at hx
  rw [conjugatePower_eq_factor s hFac j] at hy
  have hidx : (hFac.actHom a ^ (i : ℕ)) i₀ ≠ (hFac.actHom a ^ (j : ℕ)) i₀ := by
    intro heq
    exact hij (actHom_pow_injective s hFac hℓ ha ha1 hN i j heq)
  exact hFac.commute hidx hx hy

theorem orbitDiagonal_conj (hFac : IsFactorization s.Rbar S) (i₀ : Fin r)
    {a : s.Q} {ℓ : ℕ} (hℓ : 0 < ℓ) (ha : a ^ ℓ = 1)
    (hcomm : CFSG.GroupTheory.ConjugatesCommute a (S i₀) ℓ) (x : ↥(S i₀))
    {y : s.Q} (hy : y ∈ S i₀) :
    CFSG.GroupTheory.orbitDiagonalHom a (S i₀) ℓ ha hcomm x * y *
        (CFSG.GroupTheory.orbitDiagonalHom a (S i₀) ℓ ha hcomm x)⁻¹ =
      (x : s.Q) * y * (x : s.Q)⁻¹ := by
  rcases ℓ with _ | n
  · omega
  let f : Fin (n + 1) → s.Q := CFSG.GroupTheory.orbitDiagonalFactor a (n + 1) x
  let f' : Fin n → s.Q := fun i => f i.succ
  have hf_eq : f = Fin.cons (f 0) f' := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [f']
  have hδ : CFSG.GroupTheory.orbitDiagonalHom a (S i₀) (n + 1) ha hcomm x =
      (x : s.Q) * (List.ofFn f').prod := by
    change (List.ofFn f).prod = (x : s.Q) * (List.ofFn f').prod
    rw [hf_eq, List.ofFn_cons, List.prod_cons]
    simp [f, CFSG.GroupTheory.orbitDiagonalFactor]
  have hPcomm : Commute (List.ofFn f').prod y := by
    refine (Commute.list_prod_right _ _ (fun z hz => ?_)).symm
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' f' z).1 hz
    have hy0 : y ∈ CFSG.GroupTheory.conjugatePower a (S i₀) 0 := by
      rw [CFSG.GroupTheory.conjugatePower]
      simpa using Subgroup.mem_map_of_mem
        ((MulAut.conj (a ^ (0 : ℕ))).toMonoidHom) hy
    exact (hcomm i.succ 0 (by simp) _
      (CFSG.GroupTheory.orbitDiagonalFactor_mem_conjugatePower a (S i₀) (n + 1) x i.succ)
      y hy0).symm
  rw [hδ]
  calc ((x : s.Q) * (List.ofFn f').prod) * y * (((x : s.Q) * (List.ofFn f').prod))⁻¹
      = (x : s.Q) * ((List.ofFn f').prod * y * (List.ofFn f').prod⁻¹) * (x : s.Q)⁻¹ := by
        group
    _ = (x : s.Q) * y * (x : s.Q)⁻¹ := by rw [hPcomm.eq]; group

theorem factor_normalized (hFac : IsFactorization s.Rbar S) (i₀ : Fin r)
    {U : Subgroup G} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hU : U ∈ uniqueSet D.M) (hUH : U ≤ s.H) (hUY : U ⊓ s.Y = ⊥)
    (hUcard : Nat.card U = ℓ) (hUne : U ≠ ⊥) :
    s.bar U ≤ Subgroup.normalizer ((S i₀ : Subgroup s.Q) : Set s.Q) := by
  classical
  by_contra hnot
  obtain ⟨uG, huG, huG1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left hUne
  let u : ↥s.H := ⟨uG, hUH huG⟩
  have hu1 : u ≠ 1 := fun h => huG1 (Subtype.ext_iff.mp h)
  have hbarU_card : Nat.card (s.bar U) = ℓ := (s.card_bar hUH hUY).trans hUcard
  have huU : (⟨uG, huG⟩ : ↥U) ≠ 1 := fun h => huG1 (Subtype.ext_iff.mp h)
  have hord_dvd : orderOf (⟨uG, huG⟩ : ↥U) ∣ ℓ := by
    haveI : Fintype ↥U := Fintype.ofFinite _
    have h := orderOf_dvd_card (x := (⟨uG, huG⟩ : ↥U))
    rwa [← Nat.card_eq_fintype_card, hUcard] at h
  have hord_ne : orderOf (⟨uG, huG⟩ : ↥U) ≠ 1 := fun h =>
    huU ((orderOf_eq_one_iff).mp h)
  have hord : orderOf (⟨uG, huG⟩ : ↥U) = ℓ := by
    rcases (Nat.dvd_prime hℓ).mp hord_dvd with h | h
    · exact absurd h hord_ne
    · exact h
  have hupow : uG ^ ℓ = 1 := by
    have h := pow_orderOf_eq_one (⟨uG, huG⟩ : ↥U)
    rw [hord] at h
    exact congrArg Subtype.val h
  let a : s.Q := s.π u
  have ha1 : a ≠ 1 := by
    intro h
    apply hu1
    have hmem : u ∈ s.YH := (s.eq_one_iff).mp h
    have hY : (u : G) ∈ s.Y := Subgroup.mem_subgroupOf.mp hmem
    have hbot : (u : G) ∈ U ⊓ s.Y := ⟨huG, hY⟩
    rw [hUY, Subgroup.mem_bot] at hbot
    exact Subtype.ext hbot
  have hupowH : (u : ↥s.H) ^ ℓ = 1 := by
    apply Subtype.ext
    simpa using hupow
  have ha : a ^ ℓ = 1 := by
    rw [show a = s.π u from rfl, ← map_pow, hupowH, map_one]
  have hgen : s.bar U = Subgroup.zpowers a := by
    have hamem : a ∈ s.bar U := (s.mem_bar_iff hUH).mpr ⟨uG, huG, rfl⟩
    have hle : Subgroup.zpowers a ≤ s.bar U := Subgroup.zpowers_le.mpr hamem
    have hcarda : Nat.card ↥(Subgroup.zpowers a) = ℓ := by
      rw [Nat.card_zpowers]
      rcases (Nat.dvd_prime hℓ).mp (orderOf_dvd_iff_pow_eq_one.mpr ha) with h | h
      · exact absurd ((orderOf_eq_one_iff).mp h) ha1
      · exact h
    have heq : Subgroup.zpowers a = s.bar U :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hbarU_card, hcarda])
    exact heq.symm
  have hN : a ∉ Subgroup.normalizer ((S i₀ : Subgroup s.Q) : Set s.Q) := by
    intro haN
    apply hnot
    rw [hgen]
    exact Subgroup.zpowers_le.mpr haN
  have hcomm := conjugatesCommute s hFac hℓ ha ha1 hN
  have hSLne : s.bar D.T ⊓ S i₀ ≠ ⊥ := SL_ne_bot s hFac i₀
  obtain ⟨s0, hs0, hs01⟩ :=
    (Subgroup.bot_or_exists_ne_one (s.bar D.T ⊓ S i₀)).resolve_left hSLne
  have hs0L : s0 ∈ S i₀ := hs0.2
  have hs0M : s0 ∈ s.Mbar := (s.bar_le_Mbar s.T_le_H D.sylowM.le) hs0.1
  have hKne : Subgroup.normalClosure ({(⟨s0, hs0L⟩ : ↥(S i₀))} : Set ↥(S i₀)) ≠ ⊥ := by
    intro hbot
    have hmem : (⟨s0, hs0L⟩ : ↥(S i₀)) ∈ (⊥ : Subgroup ↥(S i₀)) := by
      rw [← hbot]
      exact Subgroup.subset_normalClosure (Set.mem_singleton _)
    exact hs01 (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))
  haveI : (Subgroup.normalClosure ({(⟨s0, hs0L⟩ : ↥(S i₀))} : Set ↥(S i₀))).Normal :=
    Subgroup.normalClosure_normal
  have hK : Subgroup.normalClosure ({(⟨s0, hs0L⟩ : ↥(S i₀))} : Set ↥(S i₀)) = ⊤ := by
    haveI : IsSimpleGroup ↥(S i₀) := hFac.simple i₀
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ({(⟨s0, hs0L⟩ : ↥(S i₀))} : Set ↥(S i₀))) with h | h
    · exact absurd h hKne
    · exact h
  have hconjM : ∀ x : ↥(S i₀), ((x : s.Q) * s0 * (x : s.Q)⁻¹) ∈ s.Mbar := by
    intro x
    have hδc : CFSG.GroupTheory.orbitDiagonalHom a (S i₀) ℓ ha hcomm x ∈
        Subgroup.centralizer ({a} : Set s.Q) :=
      CFSG.GroupTheory.orbitDiagonalHom_mem_centralizer a (S i₀) ℓ ha hcomm x
    have hδM : CFSG.GroupTheory.orbitDiagonalHom a (S i₀) ℓ ha hcomm x ∈ s.Mbar := by
      apply s.mem_Mbar_of_centralizes hU hUH
      rw [hgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hδc
    have hconj := orbitDiagonal_conj s hFac i₀ hℓ.pos ha hcomm x (y := s0) hs0L
    rw [← hconj]
    exact s.Mbar.mul_mem (s.Mbar.mul_mem hδM hs0M) (s.Mbar.inv_mem hδM)
  have hgenM : ∀ z ∈ Group.conjugatesOfSet ({(⟨s0, hs0L⟩ : ↥(S i₀))} : Set ↥(S i₀)),
      (z : s.Q) ∈ s.Mbar := by
    intro z hz
    obtain ⟨w, hw, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    rw [Set.mem_singleton_iff] at hw
    subst hw
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg]
    simpa using hconjM g
  have hKleM : ∀ k ∈ Subgroup.normalClosure ({(⟨s0, hs0L⟩ : ↥(S i₀))} : Set ↥(S i₀)),
      (k : s.Q) ∈ s.Mbar := by
    intro k hk
    rw [Subgroup.normalClosure] at hk
    refine Subgroup.closure_induction
      (k := Group.conjugatesOfSet ({(⟨s0, hs0L⟩ : ↥(S i₀))} : Set ↥(S i₀)))
      (p := fun x _ => (x : s.Q) ∈ s.Mbar) ?_ ?_ ?_ ?_ hk
    · exact hgenM
    · exact s.Mbar.one_mem
    · intro x y hx hy ihx ihy
      simpa using s.Mbar.mul_mem ihx ihy
    · intro x hx ih
      simpa using s.Mbar.inv_mem ih
  have hLleM : S i₀ ≤ s.Mbar := by
    intro y hy
    have hyK : (⟨y, hy⟩ : ↥(S i₀)) ∈
        Subgroup.normalClosure ({(⟨s0, hs0L⟩ : ↥(S i₀))} : Set ↥(S i₀)) := by
      rw [hK]; trivial
    exact hKleM ⟨y, hy⟩ hyK
  exact factor_not_le_Mbar s hFac i₀ hLleM

end Diagonal

section Faithfulness

variable {r : ℕ} {S : Fin r → Subgroup s.Q}

theorem bar_line_eq (D' : Subgroup s.Q) (hD'A : D' ≤ s.bar s.A) (hcard : Nat.card D' = 31)
    (hBD' : s.bar s.B ≤ Subgroup.normalizer (D' : Set s.Q)) :
    D' = s.bar s.A₁ ∨ D' = s.bar s.A₂ := by
  classical
  set Dg : Subgroup G := ((D'.comap s.π).map s.H.subtype) ⊓ s.A with hDg
  have hDA : Dg ≤ s.A := inf_le_right
  have hDH : Dg ≤ s.H := hDA.trans s.A_le_H
  have hbarD : s.bar Dg = D' := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨d, hd, rfl⟩ := (s.mem_bar_iff hDH).mp hz
      obtain ⟨x', hx'mem, hx'eq⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hd).1
      have h := Subgroup.mem_comap.mp hx'mem
      have hsub : x' = (⟨d, hDH hd⟩ : ↥s.H) := Subtype.ext hx'eq
      rwa [hsub] at h
    · intro z hz
      obtain ⟨a, ha, haz⟩ := (s.mem_bar_iff s.A_le_H).mp (hD'A hz)
      refine (s.mem_bar_iff hDH).mpr ⟨a, ?_, haz⟩
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨⟨a, s.A_le_H ha⟩, ?_, rfl⟩, ha⟩
      rwa [Subgroup.mem_comap, haz]
  have hDY : Dg ⊓ s.Y = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxD, hxY⟩ := Subgroup.mem_inf.mp hx
    have hxA : x ∈ s.A := hDA hxD
    have h1 : x ∈ s.A ⊓ s.Y := ⟨hxA, hxY⟩
    rw [s.A_inf_Y, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr h1
  have hDcard : Nat.card Dg = 31 := by
    rw [← s.card_bar hDH hDY, hbarD, hcard]
  have hBD : s.B ≤ Subgroup.normalizer (Dg : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb x hx
    obtain ⟨hxD, hxA⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨x', hx'mem, hx'eq⟩ := Subgroup.mem_map.mp hxD
    have hbAm : b * x * b⁻¹ ∈ s.A :=
      (Subgroup.mem_normalizer_iff.mp (s.B_le_normalizer_A hb) x).mp hxA
    have hbH : b * x * b⁻¹ ∈ s.H := s.A_le_H hbAm
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨⟨b * x * b⁻¹, hbH⟩, ?_, rfl⟩, hbAm⟩
    rw [Subgroup.mem_comap]
    have hbQ : s.π ⟨b, s.B_le_H hb⟩ ∈ s.bar s.B :=
      (s.mem_bar_iff s.B_le_H).mpr ⟨b, hb, rfl⟩
    have hxQ : s.π ⟨x, hDH hx⟩ ∈ D' := by
      have h := Subgroup.mem_comap.mp hx'mem
      have hsub : x' = (⟨x, hDH hx⟩ : ↥s.H) := Subtype.ext hx'eq
      rwa [hsub] at h
    have hconj := (Subgroup.mem_normalizer_iff.mp (hBD' hbQ) _).mp hxQ
    have hval : s.π (⟨b * x * b⁻¹, hbH⟩ : ↥s.H) = s.π ⟨b, s.B_le_H hb⟩ * s.π ⟨x, hDH hx⟩ *
        (s.π ⟨b, s.B_le_H hb⟩)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
    simpa [hval] using hconj
  have hlines : ∀ E : Subgroup G, E ≤ s.A → Nat.card E = 31 →
      s.B ≤ Subgroup.normalizer (E : Set G) → E = s.A₁ ∨ E = s.A₂ :=
    lines_of_case8100Four D s.hV₀ s.ctx s.h8100 s.hc4 s.hAsyl s.hAT s.hBM s.hBcard
      s.hAB s.hBT
  rcases hlines Dg hDA hDcard hBD with h | h
  · left
    rw [← hbarD, h]
  · right
    rw [← hbarD, h]

theorem bar_inf_centralizer_factor (hFac : IsFactorization s.Rbar S) (i : Fin r)
    {U : Subgroup G} {p : ℕ} (hU : U ∈ uniqueSet D.M) (hUH : U ≤ s.H)
    (hUcard : Nat.card U = p) (hp : p.Prime) :
    s.bar U ⊓ Subgroup.centralizer ((S i : Subgroup s.Q) : Set s.Q) = ⊥ := by
  have hUY : U ⊓ s.Y = ⊥ := inf_kerM_eq_bot_of_mem_uniqueSet D hU hp hUcard hUH s.hHM
  have hcard : Nat.card (s.bar U) = p := (s.card_bar hUH hUY).trans hUcard
  refine le_antisymm ?_ bot_le
  intro z hz
  obtain ⟨hzU, hzC⟩ := Subgroup.mem_inf.mp hz
  by_cases hz1 : z = 1
  · exact Subgroup.mem_bot.mpr hz1
  · have hgen : Subgroup.zpowers z = s.bar U := by
      haveI : Fact p.Prime := ⟨hp⟩
      have htop : Subgroup.zpowers (⟨z, hzU⟩ : s.bar U) = ⊤ :=
        zpowers_eq_top_of_prime_card hcard (by
          intro h
          exact hz1 (Subtype.ext_iff.mp h))
      have hmap : (Subgroup.zpowers (⟨z, hzU⟩ : s.bar U)).map (s.bar U).subtype =
          Subgroup.zpowers z := by
        rw [MonoidHom.map_zpowers]
        rfl
      rw [← hmap, htop, Subgroup.map_top, Subgroup.range_subtype]
    have hLle : S i ≤ Subgroup.centralizer ((s.bar U : Subgroup s.Q) : Set s.Q) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [← hgen] at ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact Commute.zpow_left
        (show Commute z y from (Subgroup.mem_centralizer_iff.mp hzC y hy).symm) k
    exfalso
    exact (s.factor_not_le_Mbar hFac i) fun y hy => s.mem_Mbar_of_centralizes hU hUH (hLle hy)

theorem bar_A₁_inf_centralizer_factor (hFac : IsFactorization s.Rbar S) (i : Fin r) :
    s.bar s.A₁ ⊓ Subgroup.centralizer ((S i : Subgroup s.Q) : Set s.Q) = ⊥ :=
  s.bar_inf_centralizer_factor hFac i s.A₁_mem_uniqueSet s.A₁_le_H s.A₁_card (by norm_num)

theorem bar_A₂_inf_centralizer_factor (hFac : IsFactorization s.Rbar S) (i : Fin r) :
    s.bar s.A₂ ⊓ Subgroup.centralizer ((S i : Subgroup s.Q) : Set s.Q) = ⊥ :=
  s.bar_inf_centralizer_factor hFac i s.A₂_mem_uniqueSet s.A₂_le_H s.A₂_card (by norm_num)

theorem B_ne_bot : s.B ≠ ⊥ := by
  intro h
  have h1 : Nat.card s.B = 1 := by rw [h, Subgroup.card_bot]
  rw [s.B_card5] at h1
  omega

theorem bar_B_inf_centralizer_factor (hFac : IsFactorization s.Rbar S) (i : Fin r) :
    s.bar s.B ⊓ Subgroup.centralizer ((S i : Subgroup s.Q) : Set s.Q) = ⊥ :=
  s.bar_inf_centralizer_factor hFac i s.B_mem_uniqueSet s.B_le_H s.B_card5 (by norm_num)

theorem bar_B_le_normalizer_bar_A :
    s.bar s.B ≤ Subgroup.normalizer ((s.bar s.A : Subgroup s.Q) : Set s.Q) := by
  rw [s.bar_A_eq_sup]
  exact le_trans (le_inf s.bar_B_le_normalizer_bar_A₁ s.bar_B_le_normalizer_bar_A₂)
    (Subgroup.inf_normalizer_le_normalizer_sup (s.bar s.A₁) (s.bar s.A₂))

theorem bar_B_le_normalizer_bar_A_inf_centralizer (hFac : IsFactorization s.Rbar S) (i : Fin r) :
    s.bar s.B ≤ Subgroup.normalizer
      ((s.bar s.A ⊓ Subgroup.centralizer ((S i : Subgroup s.Q) : Set s.Q) : Subgroup s.Q) :
        Set s.Q) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb z hz
  obtain ⟨hzA, hzC⟩ := Subgroup.mem_inf.mp hz
  have hbL : b ∈ Subgroup.normalizer ((S i : Subgroup s.Q) : Set s.Q) :=
    s.factor_normalized hFac i (by norm_num) s.B_mem_uniqueSet s.B_le_H s.B_inf_Y s.B_card5
      s.B_ne_bot hb
  refine Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_normalizer_iff.mp (s.bar_B_le_normalizer_bar_A hb) z).mp hzA, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : b⁻¹ * y * b ∈ S i := by
    simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hbL) y).mp hy
  have hzy := (Subgroup.mem_centralizer_iff.mp hzC) (b⁻¹ * y * b) hy'
  calc y * (b * z * b⁻¹) = b * ((b⁻¹ * y * b) * z) * b⁻¹ := by group
    _ = b * (z * (b⁻¹ * y * b)) * b⁻¹ := by rw [hzy]
    _ = (b * z * b⁻¹) * y := by group

theorem bar_A_inf_centralizer_factor (hFac : IsFactorization s.Rbar S) (i : Fin r) :
    s.bar s.A ⊓ Subgroup.centralizer ((S i : Subgroup s.Q) : Set s.Q) = ⊥ := by
  classical
  set K : Subgroup s.Q :=
    s.bar s.A ⊓ Subgroup.centralizer ((S i : Subgroup s.Q) : Set s.Q) with hK
  have hKA : K ≤ s.bar s.A := inf_le_left
  have hKnorm : s.bar s.B ≤ Subgroup.normalizer (K : Set s.Q) :=
    s.bar_B_le_normalizer_bar_A_inf_centralizer hFac i
  have hKne : K ≠ s.bar s.A := by
    intro heq
    have hAC : s.bar s.A ≤ Subgroup.centralizer ((S i : Subgroup s.Q) : Set s.Q) :=
      heq ▸ inf_le_right
    refine (s.factor_not_le_Mbar hFac i) fun y hy => s.mem_Mbar_of_centralizes s.A₁_mem_uniqueSet
      s.A₁_le_H ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hAC (s.bar_mono s.A₁_le_A ha))) y hy).symm
  have hKnot1 : ¬ s.bar s.A₁ ≤ K := by
    intro hle
    have hle' : s.bar s.A₁ ≤ s.bar s.A₁ ⊓
        Subgroup.centralizer ((S i : Subgroup s.Q) : Set s.Q) :=
      le_inf le_rfl (hle.trans inf_le_right)
    rw [s.bar_A₁_inf_centralizer_factor hFac i] at hle'
    have hbot : s.bar s.A₁ = ⊥ := le_bot_iff.mp hle'
    have h1 : Nat.card (s.bar s.A₁) = 31 := s.bar_A₁_card
    rw [hbot, Subgroup.card_bot] at h1
    omega
  have hKnot2 : ¬ s.bar s.A₂ ≤ K := by
    intro hle
    have hle' : s.bar s.A₂ ≤ s.bar s.A₂ ⊓
        Subgroup.centralizer ((S i : Subgroup s.Q) : Set s.Q) :=
      le_inf le_rfl (hle.trans inf_le_right)
    rw [s.bar_A₂_inf_centralizer_factor hFac i] at hle'
    have hbot : s.bar s.A₂ = ⊥ := le_bot_iff.mp hle'
    have h1 : Nat.card (s.bar s.A₂) = 31 := s.bar_A₂_card
    rw [hbot, Subgroup.card_bot] at h1
    omega
  have hKdvd : Nat.card K ∣ 31 ^ 2 := by
    rw [← s.bar_A_card]
    exact Subgroup.card_dvd_of_le hKA
  obtain ⟨k, hk, hkcard⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 31)).mp hKdvd
  interval_cases k
  · exact Subgroup.eq_bot_of_card_eq K hkcard
  · rcases s.bar_line_eq K hKA hkcard hKnorm with h | h
    · rw [h] at hKnot1
      exact absurd le_rfl hKnot1
    · rw [h] at hKnot2
      exact absurd le_rfl hKnot2
  · have hKeq : K = s.bar s.A :=
      Subgroup.eq_of_le_of_card_ge hKA (by rw [hkcard, s.bar_A_card])
    exact absurd hKeq hKne

end Faithfulness

section AlmostSimple

variable {r : ℕ} {S : Fin r → Subgroup s.Q}

theorem factor_inf_centralizer (hFac : IsFactorization s.Rbar S) (i : Fin r) :
    S i ⊓ Subgroup.centralizer ((S i : Subgroup s.Q) : Set s.Q) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
  haveI : IsSimpleGroup ↥(S i) := hFac.simple i
  have hnab : ¬ IsMulCommutative ↥(S i) := by
    intro h
    obtain ⟨a, b, hab⟩ := hFac.nonab i
    exact hab ((isMulCommutative_iff.mp h) a b)
  have hcenter : Subgroup.center ↥(S i) = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnab
  have hmem : (⟨x, hxS⟩ : ↥(S i)) ∈ Subgroup.center ↥(S i) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) (g : s.Q) g.2)
  rw [hcenter, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

section Quotient

@[expose] def NQ (L : Subgroup s.Q) : Subgroup s.Q := Subgroup.normalizer (L : Set s.Q)

theorem le_NQ (L : Subgroup s.Q) : L ≤ s.NQ L := Subgroup.le_normalizer

theorem normal_in_NQ (L : Subgroup s.Q) : (L.subgroupOf (s.NQ L)).Normal :=
  Subgroup.normal_in_normalizer

@[expose] def CN (L : Subgroup s.Q) : Subgroup ↥(s.NQ L) :=
  (Subgroup.centralizer (L : Set s.Q)).subgroupOf (s.NQ L)

instance CN_normal (L : Subgroup s.Q) : (s.CN L).Normal :=
  Subgroup.normal_subgroupOf_centralizer_normalizer _

abbrev Xq (L : Subgroup s.Q) : Type := ↥(s.NQ L) ⧸ s.CN L

@[expose] def ψ (L : Subgroup s.Q) : ↥(s.NQ L) →* s.Xq L := QuotientGroup.mk' (s.CN L)

theorem ψ_eq_one_iff (L : Subgroup s.Q) {u : ↥(s.NQ L)} :
    s.ψ L u = 1 ↔ (u : s.Q) ∈ Subgroup.centralizer (L : Set s.Q) :=
  (QuotientGroup.eq_one_iff (N := s.CN L) u).trans Subgroup.mem_subgroupOf

@[expose] def im (L : Subgroup s.Q) (U : Subgroup s.Q) : Subgroup (s.Xq L) :=
  (U.subgroupOf (s.NQ L)).map (s.ψ L)

theorem mem_im_iff (L : Subgroup s.Q) {U : Subgroup s.Q} (hUN : U ≤ s.NQ L) {z : s.Xq L} :
    z ∈ s.im L U ↔ ∃ (u : s.Q) (hu : u ∈ U), s.ψ L ⟨u, hUN hu⟩ = z := by
  constructor
  · intro hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨(u : s.Q), Subgroup.mem_subgroupOf.mp hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact Subgroup.mem_map_of_mem (s.ψ L) (Subgroup.mem_subgroupOf.mpr hu)

theorem im_mono (L : Subgroup s.Q) {U W : Subgroup s.Q} (h : U ≤ W) :
    s.im L U ≤ s.im L W :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

theorem im_sup (L : Subgroup s.Q) {U W : Subgroup s.Q} (hU : U ≤ s.NQ L) (hW : W ≤ s.NQ L) :
    s.im L (U ⊔ W) = s.im L U ⊔ s.im L W := by
  unfold im
  rw [Subgroup.subgroupOf_sup hU hW, Subgroup.map_sup]

theorem ψ_injective_of_inf_bot (L : Subgroup s.Q) {U : Subgroup s.Q} (hUN : U ≤ s.NQ L)
    (hUC : U ⊓ Subgroup.centralizer (L : Set s.Q) = ⊥) :
    Function.Injective (fun u : ↥U => s.ψ L ⟨(u : s.Q), hUN u.2⟩) := by
  intro u v huv
  apply Subtype.ext
  have huv' : s.ψ L ⟨(u : s.Q), hUN u.2⟩ = s.ψ L ⟨(v : s.Q), hUN v.2⟩ := huv
  have h1 : s.ψ L ((⟨(u : s.Q), hUN u.2⟩ : ↥(s.NQ L)) *
      (⟨(v : s.Q), hUN v.2⟩ : ↥(s.NQ L))⁻¹) = 1 := by
    rw [map_mul, map_inv, huv']
    simp
  have h2 : ((⟨(u : s.Q), hUN u.2⟩ : ↥(s.NQ L)) *
      (⟨(v : s.Q), hUN v.2⟩ : ↥(s.NQ L))⁻¹) ∈ s.CN L :=
    (QuotientGroup.eq_one_iff _).mp h1
  have h3 : ((u : s.Q) * (v : s.Q)⁻¹) ∈ Subgroup.centralizer (L : Set s.Q) :=
    Subgroup.mem_subgroupOf.mp h2
  have h4 : (u : s.Q) * (v : s.Q)⁻¹ ∈ U ⊓ Subgroup.centralizer (L : Set s.Q) :=
    ⟨U.mul_mem u.2 (U.inv_mem v.2), h3⟩
  rw [hUC, Subgroup.mem_bot] at h4
  calc (u : s.Q) = (u : s.Q) * (v : s.Q)⁻¹ * (v : s.Q) := by group
    _ = (v : s.Q) := by rw [h4, one_mul]

theorem ψ_injective_of_inf_bot' (L : Subgroup s.Q) {U : Subgroup s.Q} (hUN : U ≤ s.NQ L)
    (hUC : U ⊓ Subgroup.centralizer (L : Set s.Q) = ⊥) :
    Function.Injective ((s.ψ L).comp (U.subgroupOf (s.NQ L)).subtype) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  have h1 : s.ψ L ((x : ↥(s.NQ L)) * (y : ↥(s.NQ L))⁻¹) = 1 := by
    rw [map_mul, map_inv, show s.ψ L x = s.ψ L y from hxy]
    simp
  have h2 : ((x : ↥(s.NQ L)) * (y : ↥(s.NQ L))⁻¹) ∈ s.CN L :=
    (QuotientGroup.eq_one_iff _).mp h1
  have h3 : ((x : s.Q) * (y : s.Q)⁻¹) ∈ Subgroup.centralizer (L : Set s.Q) :=
    Subgroup.mem_subgroupOf.mp h2
  have hxU : (x : s.Q) ∈ U := Subgroup.mem_subgroupOf.mp x.2
  have hyU : (y : s.Q) ∈ U := Subgroup.mem_subgroupOf.mp y.2
  have h4 : (x : s.Q) * (y : s.Q)⁻¹ ∈ U ⊓ Subgroup.centralizer (L : Set s.Q) :=
    ⟨U.mul_mem hxU (U.inv_mem hyU), h3⟩
  rw [hUC, Subgroup.mem_bot] at h4
  calc (x : s.Q) = (x : s.Q) * (y : s.Q)⁻¹ * (y : s.Q) := by group
    _ = (y : s.Q) := by rw [h4, one_mul]

theorem card_im (L : Subgroup s.Q) {U : Subgroup s.Q} (hUN : U ≤ s.NQ L)
    (hUC : U ⊓ Subgroup.centralizer (L : Set s.Q) = ⊥) :
    Nat.card (s.im L U) = Nat.card U := by
  classical
  have hinj := s.ψ_injective_of_inf_bot L hUN hUC
  let f : ↥U → ↥(s.im L U) := fun u =>
    ⟨s.ψ L ⟨(u : s.Q), hUN u.2⟩,
      Subgroup.mem_map_of_mem (s.ψ L) (Subgroup.mem_subgroupOf.mpr u.2)⟩
  have hfinj : Function.Injective f := by
    intro u v huv
    exact hinj (congrArg Subtype.val huv)
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨u, hu, huz⟩ := (s.mem_im_iff L hUN).mp z.2
    exact ⟨⟨u, hu⟩, Subtype.ext huz⟩
  calc Nat.card (s.im L U) = Nat.card ↥U :=
        (Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)).symm
    _ = Nat.card U := rfl

theorem exists_preimage (L : Subgroup s.Q) {U : Subgroup s.Q} (hUN : U ≤ s.NQ L)
    {D' : Subgroup (s.Xq L)} (hD' : D' ≤ s.im L U) :
    ∃ D : Subgroup s.Q, D ≤ U ∧ s.im L D = D' := by
  classical
  refine ⟨((D'.comap (s.ψ L)).map (s.NQ L).subtype) ⊓ U, inf_le_right, ?_⟩
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hz
    have hnD : (n : s.Q) ∈ ((D'.comap (s.ψ L)).map (s.NQ L).subtype) ⊓ U :=
      Subgroup.mem_subgroupOf.mp hn
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hnD).1
    have hmn' : m = n := Subtype.ext hmn
    rw [hmn'] at hm
    exact Subgroup.mem_comap.mp hm
  · intro z hz
    obtain ⟨u, hu, huz⟩ := (s.mem_im_iff L hUN).mp (hD' hz)
    refine Subgroup.mem_map.mpr ⟨⟨u, hUN hu⟩, ?_, huz⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    refine Subgroup.mem_inf.mpr ⟨?_, hu⟩
    refine Subgroup.mem_map.mpr ⟨⟨u, hUN hu⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, huz]
    exact hz

end Quotient

section Images

@[expose] def L' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    Subgroup (s.Xq (S i₀)) := s.im (S i₀) (S i₀)

@[expose] def A₁' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    Subgroup (s.Xq (S i₀)) := s.im (S i₀) (s.bar s.A₁)

@[expose] def A₂' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    Subgroup (s.Xq (S i₀)) := s.im (S i₀) (s.bar s.A₂)

@[expose] def Abar' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    Subgroup (s.Xq (S i₀)) := s.im (S i₀) (s.bar s.A)

@[expose] def B' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    Subgroup (s.Xq (S i₀)) := s.im (S i₀) (s.bar s.B)

@[expose] def T' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    Subgroup (s.Xq (S i₀)) := s.im (S i₀) (s.bar D.T)

@[expose] def TSL (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    Subgroup s.Q := s.bar D.T ⊓ S i₀

@[expose] def TL (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    Subgroup s.Q := s.bar D.T ⊓ s.NQ (S i₀)

@[expose] def TSL' (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    Subgroup (s.Xq (S i₀)) := s.im (S i₀) (s.TSL hFac i₀)

@[expose] def ML (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    Subgroup (s.Xq (S i₀)) := s.im (S i₀) (s.Mbar ⊓ S i₀)

theorem A₁_ne_bot : s.A₁ ≠ ⊥ := by
  intro h
  have h1 : Nat.card s.A₁ = 1 := by rw [h, Subgroup.card_bot]
  rw [s.A₁_card] at h1
  omega

theorem A₂_ne_bot : s.A₂ ≠ ⊥ := by
  intro h
  have h1 : Nat.card s.A₂ = 1 := by rw [h, Subgroup.card_bot]
  rw [s.A₂_card] at h1
  omega

theorem bar_A₁_le_N (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    s.bar s.A₁ ≤ s.NQ (S i₀) :=
  s.factor_normalized hFac i₀ (by norm_num) s.A₁_mem_uniqueSet s.A₁_le_H s.A₁_inf_Y
    s.A₁_card s.A₁_ne_bot

theorem bar_A₂_le_N (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    s.bar s.A₂ ≤ s.NQ (S i₀) :=
  s.factor_normalized hFac i₀ (by norm_num) s.A₂_mem_uniqueSet s.A₂_le_H s.A₂_inf_Y
    s.A₂_card s.A₂_ne_bot

theorem bar_A_le_N (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    s.bar s.A ≤ s.NQ (S i₀) := by
  rw [s.bar_A_eq_sup]
  exact sup_le (s.bar_A₁_le_N hFac i₀) (s.bar_A₂_le_N hFac i₀)

theorem bar_B_le_N (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    s.bar s.B ≤ s.NQ (S i₀) :=
  s.factor_normalized hFac i₀ (by norm_num) s.B_mem_uniqueSet s.B_le_H s.B_inf_Y
    s.B_card5 s.B_ne_bot

theorem Abar'_eq_sup (hFac : IsFactorization s.Rbar S) (i₀ : Fin r) :
    s.Abar' hFac i₀ = s.A₁' hFac i₀ ⊔ s.A₂' hFac i₀ := by
  have hsup : s.bar s.A = s.bar s.A₁ ⊔ s.bar s.A₂ := s.bar_A_eq_sup
  rw [Abar', hsup, s.im_sup (S i₀) (s.bar_A₁_le_N hFac i₀) (s.bar_A₂_le_N hFac i₀)]
  rfl

end Images

section Properties

variable (hFac : IsFactorization s.Rbar S) (i₀ : Fin r)

theorem L'_normal : (s.L' hFac i₀).Normal :=
  (s.normal_in_NQ (S i₀)).map (s.ψ (S i₀)) (QuotientGroup.mk'_surjective _)

@[expose] noncomputable def L_equiv : ↥(S i₀) ≃* ↥(s.L' hFac i₀) :=
  MulEquiv.ofBijective
    (((s.ψ (S i₀)).subgroupMap ((S i₀).subgroupOf (s.NQ (S i₀)))).comp
      (Subgroup.subgroupOfEquivOfLe (s.le_NQ (S i₀))).symm.toMonoidHom)
    ⟨by
      intro x y hxy
      apply s.ψ_injective_of_inf_bot (S i₀) (s.le_NQ (S i₀)) (s.factor_inf_centralizer hFac i₀)
      exact congrArg Subtype.val hxy,
    by
      intro z
      obtain ⟨n, hn, hnz⟩ := Subgroup.mem_map.mp z.2
      refine ⟨(Subgroup.subgroupOfEquivOfLe (s.le_NQ (S i₀))) ⟨n, hn⟩, ?_⟩
      exact Subtype.ext hnz⟩

theorem L'_simple : IsSimpleGroup ↥(s.L' hFac i₀) := by
  haveI : IsSimpleGroup ↥(S i₀) := hFac.simple i₀
  exact MulEquiv.isSimpleGroup (s.L_equiv hFac i₀).symm

theorem L'_nonab : ¬ IsMulCommutative ↥(s.L' hFac i₀) := by
  intro h
  obtain ⟨a, b, hab⟩ := hFac.nonab i₀
  have hc := (isMulCommutative_iff.mp h) (s.L_equiv hFac i₀ a) (s.L_equiv hFac i₀ b)
  refine hab ((s.L_equiv hFac i₀).injective ?_)
  simpa using hc

theorem L'_K : CFSG.Open.IsKGroup ↥(s.L' hFac i₀) := by
  have hNne : s.N ≠ ⊤ := CFSG.LocalAnalysis.UniquenessCase.UC9R96.ne_top_of_mem_calMOf D s.hN
  have hH : s.H ≠ ⊤ := by
    intro h
    exact hNne (top_le_iff.mp (h ▸ s.hHN))
  haveI hYH : (s.Y.subgroupOf s.H).Normal := s.YH_normal
  have hK : CFSG.Open.IsKGroup ↥(S i₀) :=
    CFSG.Open.IsKGroup.subgroup
      (CFSG.Open.IsKGroup.quotient (CFSG.Open.IsKProper.isKGroup D.standing.kProper s.H hH)
        (s.Y.subgroupOf s.H)) (S i₀)
  have hK' : CFSG.Open.IsKGroup ↥((S i₀).subgroupOf (s.NQ (S i₀))) :=
    CFSG.Open.IsKGroup.of_surjective hK
      (Subgroup.subgroupOfEquivOfLe (s.le_NQ (S i₀))).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (s.le_NQ (S i₀))).symm.surjective
  exact isKGroup_map_of_injective hK' (s.ψ (S i₀))
    (s.ψ_injective_of_inf_bot' (S i₀) (s.le_NQ (S i₀)) (s.factor_inf_centralizer hFac i₀))

theorem centralizer_L'_eq_bot : Subgroup.centralizer ((s.L' hFac i₀ : Subgroup (s.Xq (S i₀))) :
    Set (s.Xq (S i₀))) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (s.CN (S i₀)) x
  have hmem : (n : s.Q) ∈ Subgroup.centralizer ((S i₀ : Subgroup s.Q) : Set s.Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyl : s.ψ (S i₀) ⟨y, s.le_NQ (S i₀) hy⟩ ∈ s.L' hFac i₀ :=
      Subgroup.mem_map_of_mem (s.ψ (S i₀)) (Subgroup.mem_subgroupOf.mpr hy)
    have hcomm : s.ψ (S i₀) ⟨y, s.le_NQ (S i₀) hy⟩ * s.ψ (S i₀) n =
        s.ψ (S i₀) n * s.ψ (S i₀) ⟨y, s.le_NQ (S i₀) hy⟩ :=
      (Subgroup.mem_centralizer_iff.mp hx) _ hyl
    have h1 : s.ψ (S i₀) ((⟨y, s.le_NQ (S i₀) hy⟩ : ↥(s.NQ (S i₀))) * n *
        (⟨y, s.le_NQ (S i₀) hy⟩ : ↥(s.NQ (S i₀)))⁻¹ * n⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h2 : ((⟨y, s.le_NQ (S i₀) hy⟩ : ↥(s.NQ (S i₀))) * n *
        (⟨y, s.le_NQ (S i₀) hy⟩ : ↥(s.NQ (S i₀)))⁻¹ * n⁻¹) ∈ s.CN (S i₀) :=
      (QuotientGroup.eq_one_iff _).mp h1
    have h3 : (y * (n : s.Q) * y⁻¹ * (n : s.Q)⁻¹) ∈
        Subgroup.centralizer ((S i₀ : Subgroup s.Q) : Set s.Q) := Subgroup.mem_subgroupOf.mp h2
    have hny : (n : s.Q) * y * (n : s.Q)⁻¹ ∈ S i₀ :=
      (Subgroup.mem_normalizer_iff.mp n.2 y).mp hy
    have h3L : y * (n : s.Q) * y⁻¹ * (n : s.Q)⁻¹ ∈ S i₀ := by
      have h4 : y * ((n : s.Q) * y * (n : s.Q)⁻¹)⁻¹ ∈ S i₀ :=
        (S i₀).mul_mem hy ((S i₀).inv_mem hny)
      simpa [mul_assoc] using h4
    have h5 : (y * (n : s.Q) * y⁻¹ * (n : s.Q)⁻¹) ∈
        S i₀ ⊓ Subgroup.centralizer ((S i₀ : Subgroup s.Q) : Set s.Q) := ⟨h3L, h3⟩
    rw [s.factor_inf_centralizer hFac i₀, Subgroup.mem_bot] at h5
    calc y * (n : s.Q) = (y * (n : s.Q) * y⁻¹ * (n : s.Q)⁻¹) * ((n : s.Q) * y) := by group
      _ = (n : s.Q) * y := by rw [h5, one_mul]
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff n).mpr (Subgroup.mem_subgroupOf.mpr hmem)

theorem card_L' : Nat.card (s.L' hFac i₀) = Nat.card (S i₀) :=
  s.card_im (S i₀) (s.le_NQ (S i₀)) (s.factor_inf_centralizer hFac i₀)

theorem card_A₁' : Nat.card (s.A₁' hFac i₀) = 31 :=
  (s.card_im (S i₀) (s.bar_A₁_le_N hFac i₀) (s.bar_A₁_inf_centralizer_factor hFac i₀)).trans
    s.bar_A₁_card

theorem card_A₂' : Nat.card (s.A₂' hFac i₀) = 31 :=
  (s.card_im (S i₀) (s.bar_A₂_le_N hFac i₀) (s.bar_A₂_inf_centralizer_factor hFac i₀)).trans
    s.bar_A₂_card

theorem card_B' : Nat.card (s.B' hFac i₀) = 5 :=
  (s.card_im (S i₀) (s.bar_B_le_N hFac i₀) (s.bar_B_inf_centralizer_factor hFac i₀)).trans
    s.bar_B_card

theorem TSL_le_N : s.TSL hFac i₀ ≤ s.NQ (S i₀) := inf_le_right.trans (s.le_NQ (S i₀))

theorem TL_le_N : s.TL hFac i₀ ≤ s.NQ (S i₀) := inf_le_right

theorem TSL_le_TL : s.TSL hFac i₀ ≤ s.TL hFac i₀ :=
  le_inf inf_le_left (inf_le_right.trans (s.le_NQ (S i₀)))

theorem TSL_inf_centralizer : s.TSL hFac i₀ ⊓
    Subgroup.centralizer ((S i₀ : Subgroup s.Q) : Set s.Q) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro z hz
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
  have h3 : z ∈ S i₀ ⊓ Subgroup.centralizer ((S i₀ : Subgroup s.Q) : Set s.Q) :=
    ⟨(Subgroup.mem_inf.mp hz1).2, hz2⟩
  rw [s.factor_inf_centralizer hFac i₀, Subgroup.mem_bot] at h3
  exact Subgroup.mem_bot.mpr h3

theorem card_TSL' : Nat.card (s.TSL' hFac i₀) = Nat.card (s.TSL hFac i₀) :=
  s.card_im (S i₀) (s.TSL_le_N hFac i₀) (s.TSL_inf_centralizer hFac i₀)

end Properties

end AlmostSimple

end Data

end ChiefSetup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
