module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalPairs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Chamber
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCommuteAnchor
import CFSG.Permutation.SymmetricCoxeter

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs

theorem exists_normalizer_conjAut_eq_permAut_of_join {G : Type} [Group G] [Finite G] {p n : ℕ}
    {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (τ : Equiv.Perm (Fin n)) :
    ∃ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)), g ∈ L ⊔ ⨆ K ∈ 𝒦, K ∧
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ := by
  have hperm : SpCoord.permAut (p := p) τ ∈ bSignedFull n p :=
    aPermutationFull_le_bSignedFull (permAut_mem_aPermutationFull (p := p) τ)
  have hmem : SpCoord.permAut (p := p) τ ∈
      (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom := by
    rw [h𝒦]
    exact hperm
  have hmem' : SpCoord.permAut (p := p) τ ∈
      (ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs).map (MulAut.congr eta).toMonoidHom :=
    (Subgroup.map_mono (ggAutomizerJoin_le_ggAutomizer L Bs 𝒦)) hmem
  exact exists_mem_of_mem_map_congr (Bs := Bs) (W := L ⊔ ⨆ K ∈ 𝒦, K) eta hmem'

section Crossing

variable {G : Type} [Group G] [Finite G] {p n r f : ℕ} [Fact p.Prime]
  {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
  {E : QuadExt F K (unitaryInvolution K 2 f)}

theorem GGSecFiveBPermOmKFrame.normPerm_swap_commute_ggBlockComm
    {Bs X : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 1) ≃ Fin n}
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hκ : GGSecFiveBPermOmKFrame E Bs X eta π κ χ)
    (hperm : ∀ τ : Equiv.Perm (Fin n), ∃ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ)
    (hr : 3 ≤ r) (hn : 6 ≤ n) {i j : Fin r} (hij : i ≠ j) {c d : Fin n} (hcd : c ≠ d)
    (hdisj : Disjoint ({π i.castSucc, π j.castSucc} : Finset (Fin n)) {c, d}) :
    ∀ z ∈ ggBlockComm Bs eta ({c, d} : Set (Fin n)),
      Commute (κ (normPerm E hr (Equiv.swap i j))) z := by
  classical
  have hrn : r + 1 = n := by
    simpa using Fintype.card_congr π
  set a : Fin n := π (Fin.last r) with ha_def
  have hι_ne_a : ∀ t : Fin r, π t.castSucc ≠ a := fun t h =>
    Fin.castSucc_ne_last t (π.injective h)
  have hι_inj : ∀ t₁ t₂ : Fin r, π t₁.castSucc = π t₂.castSucc → t₁ = t₂ := fun t₁ t₂ h =>
    Fin.castSucc_injective r (π.injective h)
  have hrep : ∀ t : Fin n, t ≠ a → ∃ t' : Fin r, π t'.castSucc = t := by
    intro t ht
    have hlast : π.symm t ≠ Fin.last r := fun h => ht (by rw [ha_def, ← h, Equiv.apply_symm_apply])
    obtain ⟨t', ht'⟩ := Fin.exists_castSucc_eq.mpr hlast
    exact ⟨t', by rw [ht', Equiv.apply_symm_apply]⟩
  have hpick : ∀ s : Finset (Fin n), s.card < n → ∃ e, e ∉ s := by
    intro s hs
    by_contra h
    have hall : ∀ x, x ∈ s := fun x => by
      by_contra hx
      exact h ⟨x, hx⟩
    have hle := Finset.card_le_card (fun x (_ : x ∈ (Finset.univ : Finset (Fin n))) => hall x)
    rw [Finset.card_univ, Fintype.card_fin] at hle
    omega
  have hblk : ∀ t₁ t₂ : Fin r, t₁ ≠ t₂ →
      ggBlockComm Bs eta ({π t₁.castSucc, π t₂.castSucc} : Set (Fin n)) =
        (normBlock E r {t₁, t₂}).map κ := by
    intro t₁ t₂ ht
    have hcard : ({t₁, t₂} : Finset (Fin r)).card = 2 := Finset.card_pair ht
    have h := GGSecFiveBPermOmKFrame.blockComm_eq_map_normBlock hBs hyB hX hκ
      (S := ({t₁, t₂} : Finset (Fin r))) (by omega) (by omega)
    simpa [Set.image_pair] using h
  have hnat : ∀ t₁ t₂ : Fin r, t₁ ≠ t₂ → t₁ ≠ i → t₁ ≠ j → t₂ ≠ i → t₂ ≠ j →
      ∀ w ∈ ggBlockComm Bs eta ({π t₁.castSucc, π t₂.castSucc} : Set (Fin n)),
        Commute (κ (normPerm E hr (Equiv.swap i j))) w := by
    intro t₁ t₂ ht h1i h1j h2i h2j w hw
    rw [hblk t₁ t₂ ht] at hw
    obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.mp hw
    have h := normPerm_commute_normBlock_pair E hr ht (Equiv.swap i j) ⟨β, hβ⟩
      (Equiv.swap_apply_of_ne_of_ne h1i h1j) (Equiv.swap_apply_of_ne_of_ne h2i h2j)
    have h' := congrArg κ h
    rw [map_mul, map_mul] at h'
    exact h'
  have hPc : c ≠ π i.castSucc ∧ c ≠ π j.castSucc := by
    have h := Finset.disjoint_right.mp hdisj (by simp : c ∈ ({c, d} : Finset (Fin n)))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact h
  have hPd : d ≠ π i.castSucc ∧ d ≠ π j.castSucc := by
    have h := Finset.disjoint_right.mp hdisj (by simp : d ∈ ({c, d} : Finset (Fin n)))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact h
  have key : ∀ c : Fin n, c ≠ a → c ≠ π i.castSucc → c ≠ π j.castSucc →
      ∀ z ∈ ggBlockComm Bs eta ({c, a} : Set (Fin n)),
        Commute (κ (normPerm E hr (Equiv.swap i j))) z := by
    intro c hca hci hcj z hz
    obtain ⟨c', rfl⟩ := hrep c hca
    obtain ⟨e, he⟩ := hpick {π i.castSucc, π j.castSucc, π c'.castSucc, a}
      (lt_of_le_of_lt (Finset.card_le_four) (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    obtain ⟨hei, hej, hec, hea⟩ := he
    obtain ⟨e', rfl⟩ := hrep e hea
    obtain ⟨k₁, hk₁⟩ := hpick {π i.castSucc, π j.castSucc, a, π e'.castSucc}
      (lt_of_le_of_lt (Finset.card_le_four) (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk₁
    obtain ⟨hk₁i, hk₁j, hk₁a, hk₁e⟩ := hk₁
    obtain ⟨k₂, hk₂⟩ := hpick {π i.castSucc, π j.castSucc, a, π e'.castSucc, k₁}
      (lt_of_le_of_lt (Finset.card_le_five) (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk₂
    obtain ⟨hk₂i, hk₂j, hk₂a, hk₂e, hk₂k₁⟩ := hk₂
    obtain ⟨k₁', rfl⟩ := hrep k₁ hk₁a
    obtain ⟨k₂', rfl⟩ := hrep k₂ hk₂a
    have hk' : k₁' ≠ k₂' := fun h => hk₂k₁ (by rw [h])
    have hne : ∀ {t t' : Fin r}, π t.castSucc ≠ π t'.castSucc → t ≠ t' := fun h h' =>
      h (by rw [h'])
    obtain ⟨g, hg, hgτ⟩ := hperm (Equiv.swap a (π e'.castSucc))
    have hconj := fun S => ggBlockComm_map_conj (eta := eta) hg hgτ S
    have hfixP : (Equiv.swap a (π e'.castSucc)) ''
        ({π i.castSucc, π j.castSucc} : Set (Fin n)) = {π i.castSucc, π j.castSucc} := by
      rw [Set.image_pair, Equiv.swap_apply_of_ne_of_ne (hι_ne_a i) (Ne.symm hei),
        Equiv.swap_apply_of_ne_of_ne (hι_ne_a j) (Ne.symm hej)]
    have hfixT : (Equiv.swap a (π e'.castSucc)) ''
        ({π k₁'.castSucc, π k₂'.castSucc} : Set (Fin n)) =
          {π k₁'.castSucc, π k₂'.castSucc} := by
      rw [Set.image_pair, Equiv.swap_apply_of_ne_of_ne hk₁a hk₁e,
        Equiv.swap_apply_of_ne_of_ne hk₂a hk₂e]
    have hmoveQ : (Equiv.swap a (π e'.castSucc)) '' ({π c'.castSucc, a} : Set (Fin n)) =
        {π c'.castSucc, π e'.castSucc} := by
      rw [Set.image_pair, Equiv.swap_apply_of_ne_of_ne hca (Ne.symm hec),
        Equiv.swap_apply_left]
    let z₀ : G := κ (normPerm E hr (Equiv.swap i j))
    have hz₀ : z₀ ∈ ggBlockComm Bs eta ({π i.castSucc, π j.castSucc} : Set (Fin n)) := by
      rw [hblk i j hij]
      exact Subgroup.mem_map_of_mem κ (normPerm_swap_mem_normBlock (E := E) hr i j)
    have hgz₀ : (MulAut.conj g).toMonoidHom z₀ ∈
        ggBlockComm Bs eta ({π i.castSucc, π j.castSucc} : Set (Fin n)) := by
      rw [← hfixP, ← hconj]
      exact Subgroup.mem_map_of_mem _ hz₀
    rw [hblk i j hij] at hgz₀
    obtain ⟨α, hα, hαg⟩ := Subgroup.mem_map.mp hgz₀
    have hαcomm : ∀ β ∈ normBlock E r {k₁', k₂'}, Commute α β := by
      intro β hβ
      have hκβ : κ β ∈ ggBlockComm Bs eta ({π k₁'.castSucc, π k₂'.castSucc} : Set (Fin n)) := by
        rw [hblk k₁' k₂' hk']
        exact Subgroup.mem_map_of_mem κ hβ
      rw [← hfixT, ← hconj] at hκβ
      obtain ⟨w, hw, hwβ⟩ := Subgroup.mem_map.mp hκβ
      have hzw : Commute z₀ w :=
        hnat k₁' k₂' hk' (hne hk₁i) (hne hk₁j) (hne hk₂i) (hne hk₂j) w hw
      have hc : Commute (κ α) (κ β) := by
        rw [hαg, ← hwβ]
        exact hzw.map _
      apply hκ.1
      rw [map_mul, map_mul]
      exact hc.eq
    have hfix := fixes_anchor_of_commute_normBlock E (by omega : 2 ≤ r)
      (S := {k₁', k₂'}) (by rw [Finset.card_pair hk']) hαcomm
    have hgz : (MulAut.conj g).toMonoidHom z ∈
        ggBlockComm Bs eta ({π c'.castSucc, π e'.castSucc} : Set (Fin n)) := by
      rw [← hmoveQ, ← hconj]
      exact Subgroup.mem_map_of_mem _ hz
    have hce : c' ≠ e' := hne (Ne.symm hec)
    rw [hblk c' e' hce] at hgz
    obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.mp hgz
    have hdisj' : Disjoint ({i, j} : Finset (Fin r)) {c', e'} := by
      rw [Finset.disjoint_left]
      intro t ht ht'
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht ht'
      rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
      exacts [hci rfl, hei rfl, hcj rfl, hej rfl]
    have hαγ : Commute α γ :=
      normBlock_commute_of_disjoint_of_fix_anchor hdisj' hα hγ hfix
    have hcg : Commute ((MulAut.conj g).toMonoidHom z₀) ((MulAut.conj g).toMonoidHom z) := by
      rw [← hαg, ← hγg]
      exact hαγ.map κ
    apply (MulAut.conj g).injective
    have h := hcg.eq
    simp only [MulEquiv.coe_toMonoidHom] at h
    rw [map_mul, map_mul]
    exact h
  intro z hz
  by_cases hac : a = c
  · have hpair : ({c, d} : Set (Fin n)) = {d, a} := by
      rw [hac, Set.pair_comm]
    rw [hpair] at hz
    exact key d (fun h => hcd (hac.symm.trans h.symm)) hPd.1 hPd.2 z hz
  · by_cases had : a = d
    · rw [← had] at hz
      exact key c (Ne.symm hac) hPc.1 hPc.2 z hz
    · obtain ⟨c', rfl⟩ := hrep c (Ne.symm hac)
      obtain ⟨d', rfl⟩ := hrep d (Ne.symm had)
      have hc'd' : c' ≠ d' := fun h => hcd (by rw [h])
      exact hnat c' d' hc'd' (fun h => hPc.1 (by rw [h])) (fun h => hPc.2 (by rw [h]))
        (fun h => hPd.1 (by rw [h])) (fun h => hPd.2 (by rw [h])) z hz

theorem GGSecFiveBPermOmKFrame.normPerm_swap_commute_of_frames
    {Bs X₁ X₂ : Subgroup G} {y₁ y₂ : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hy₁ : y₁ ∈ Bs) (hX₁ : CFSG.Open.IsComponentOf X₁ (Subgroup.centralizer ({y₁} : Set G)))
    (hy₂ : y₂ ∈ Bs) (hX₂ : CFSG.Open.IsComponentOf X₂ (Subgroup.centralizer ({y₂} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hperm : ∀ τ : Equiv.Perm (Fin n), ∃ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)),
      MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ)
    {π₁ : Fin (r + 1) ≃ Fin n} {κ₁ : normOmega E r →* G} {χ₁ : Multiplicative (ZMod p) →* Kˣ}
    (h₁ : GGSecFiveBPermOmKFrame E Bs X₁ eta π₁ κ₁ χ₁)
    {F' K' : Type} [Field F'] [Field K'] [Algebra F' K'] [Finite K'] [CharP K' 2] {f' s : ℕ}
    {E' : QuadExt F' K' (unitaryInvolution K' 2 f')}
    {π₂ : Fin (s + 1) ≃ Fin n} {κ₂ : normOmega E' s →* G} {χ₂ : Multiplicative (ZMod p) →* K'ˣ}
    (h₂ : GGSecFiveBPermOmKFrame E' Bs X₂ eta π₂ κ₂ χ₂)
    (hr : 3 ≤ r) (hs : 3 ≤ s) (hn : 6 ≤ n) {i j : Fin r} (hij : i ≠ j) {u v : Fin s}
    (huv : u ≠ v)
    (hdisj : Disjoint ({π₁ i.castSucc, π₁ j.castSucc} : Finset (Fin n))
      {π₂ u.castSucc, π₂ v.castSucc}) :
    Commute (κ₁ (normPerm E hr (Equiv.swap i j))) (κ₂ (normPerm E' hs (Equiv.swap u v))) := by
  classical
  have hsn : s + 1 = n := by
    simpa using Fintype.card_congr π₂
  have hcard : ({u, v} : Finset (Fin s)).card = 2 := Finset.card_pair huv
  have hblk := GGSecFiveBPermOmKFrame.blockComm_eq_map_normBlock hBs hy₂ hX₂ h₂
    (S := ({u, v} : Finset (Fin s))) (by omega) (by omega)
  have hy : κ₂ (normPerm E' hs (Equiv.swap u v)) ∈
      ggBlockComm Bs eta ({π₂ u.castSucc, π₂ v.castSucc} : Set (Fin n)) := by
    have hmem : κ₂ (normPerm E' hs (Equiv.swap u v)) ∈
        (normBlock E' s ({u, v} : Finset (Fin s))).map κ₂ :=
      Subgroup.mem_map_of_mem _ (normPerm_swap_mem_normBlock (E := E') hs u v)
    rw [← hblk] at hmem
    simpa [Set.image_pair] using hmem
  have huv' : π₂ u.castSucc ≠ π₂ v.castSucc := fun h =>
    huv (Fin.castSucc_injective s (π₂.injective h))
  exact GGSecFiveBPermOmKFrame.normPerm_swap_commute_ggBlockComm hBs hy₁ hX₁ h₁ hperm hr hn hij
    huv' hdisj _ hy

theorem GGSecFiveBPermOmKFrame.normPerm_swap_commute_of_frames_of_join
    {Bs X₁ X₂ L : Subgroup G} {y₁ y₂ : G} {𝒦 : Finset (Subgroup G)}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hy₁ : y₁ ∈ Bs) (hX₁ : CFSG.Open.IsComponentOf X₁ (Subgroup.centralizer ({y₁} : Set G)))
    (hy₂ : y₂ ∈ Bs) (hX₂ : CFSG.Open.IsComponentOf X₂ (Subgroup.centralizer ({y₂} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {π₁ : Fin (r + 1) ≃ Fin n} {κ₁ : normOmega E r →* G} {χ₁ : Multiplicative (ZMod p) →* Kˣ}
    (h₁ : GGSecFiveBPermOmKFrame E Bs X₁ eta π₁ κ₁ χ₁)
    {F' K' : Type} [Field F'] [Field K'] [Algebra F' K'] [Finite K'] [CharP K' 2] {f' s : ℕ}
    {E' : QuadExt F' K' (unitaryInvolution K' 2 f')}
    {π₂ : Fin (s + 1) ≃ Fin n} {κ₂ : normOmega E' s →* G} {χ₂ : Multiplicative (ZMod p) →* K'ˣ}
    (h₂ : GGSecFiveBPermOmKFrame E' Bs X₂ eta π₂ κ₂ χ₂)
    (hr : 3 ≤ r) (hs : 3 ≤ s) (hn : 6 ≤ n) {i j : Fin r} (hij : i ≠ j) {u v : Fin s}
    (huv : u ≠ v)
    (hdisj : Disjoint ({π₁ i.castSucc, π₁ j.castSucc} : Finset (Fin n))
      {π₂ u.castSucc, π₂ v.castSucc}) :
    Commute (κ₁ (normPerm E hr (Equiv.swap i j))) (κ₂ (normPerm E' hs (Equiv.swap u v))) := by
  refine GGSecFiveBPermOmKFrame.normPerm_swap_commute_of_frames hBs hy₁ hX₁ hy₂ hX₂ ?_ h₁ h₂
    hr hs hn hij huv hdisj
  intro τ
  obtain ⟨g, hg, -, hgτ⟩ := exists_normalizer_conjAut_eq_permAut_of_join h𝒦 τ
  exact ⟨g, hg, hgτ⟩

open CFSG.Permutation.SymmetricCoxeter in
theorem GGSecFiveBPermOmKFrame.exists_permHom_of_overlap_of_join
    {Bs X₁ X₂ L : Subgroup G} {y₁ y₂ : G} {𝒦 : Finset (Subgroup G)} {k : ℕ}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hy₁ : y₁ ∈ Bs) (hX₁ : CFSG.Open.IsComponentOf X₁ (Subgroup.centralizer ({y₁} : Set G)))
    (hy₂ : y₂ ∈ Bs) (hX₂ : CFSG.Open.IsComponentOf X₂ (Subgroup.centralizer ({y₂} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    {π₁ π₂ : Fin (k + 4) ≃ Fin n} {κ₁ κ₂ : normOmega E (k + 3) →* G}
    {χ₁ χ₂ : Multiplicative (ZMod p) →* Kˣ}
    (h₁ : GGSecFiveBPermOmKFrame E Bs X₁ eta π₁ κ₁ χ₁)
    (h₂ : GGSecFiveBPermOmKFrame E Bs X₂ eta π₂ κ₂ χ₂)
    (hk : 2 ≤ k) (hπ : π₂ = (finRotate (k + 4)).trans π₁)
    (hOverlap : (κ₁.comp (normPerm E (by omega : 3 ≤ k + 3))).comp
        (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 2))) =
      (κ₂.comp (normPerm E (by omega : 3 ≤ k + 3))).comp
        (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 2) ↪ Fin (k + 3)))) :
    ∃ t : Equiv.Perm (Fin (k + 4)) →* G,
      t.comp (Equiv.Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4))) =
        κ₁.comp (normPerm E (by omega : 3 ≤ k + 3)) ∧
      t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 3))) =
        κ₂.comp (normPerm E (by omega : 3 ≤ k + 3)) := by
  classical
  have hn : 6 ≤ n := by
    have h := Fintype.card_congr π₁
    simp only [Fintype.card_fin] at h
    omega
  have hrot_u : finRotate (k + 4) (Fin.castSucc (⟨k + 1, by omega⟩ : Fin (k + 3))) =
      (⟨k + 2, by omega⟩ : Fin (k + 4)) := by
    simpa using finRotate_of_lt (n := k + 3) (k := k + 1) (by omega : k + 1 < k + 3)
  have hrot_v : finRotate (k + 4) (Fin.castSucc (⟨k + 2, by omega⟩ : Fin (k + 3))) =
      (⟨k + 3, by omega⟩ : Fin (k + 4)) := by
    simpa using finRotate_of_lt (n := k + 3) (k := k + 2) (by omega : k + 2 < k + 3)
  have hπ₂_u : π₂ (Fin.castSucc (⟨k + 1, by omega⟩ : Fin (k + 3))) =
      π₁ (⟨k + 2, by omega⟩ : Fin (k + 4)) := by
    rw [hπ, Equiv.trans_apply, hrot_u]
  have hπ₂_v : π₂ (Fin.castSucc (⟨k + 2, by omega⟩ : Fin (k + 3))) =
      π₁ (⟨k + 3, by omega⟩ : Fin (k + 4)) := by
    rw [hπ, Equiv.trans_apply, hrot_v]
  have hdisj : Disjoint
      ({π₁ (Fin.castSucc (⟨0, by omega⟩ : Fin (k + 3))),
        π₁ (Fin.castSucc (⟨1, by omega⟩ : Fin (k + 3)))} : Finset (Fin n))
      ({π₂ (Fin.castSucc (⟨k + 1, by omega⟩ : Fin (k + 3))),
        π₂ (Fin.castSucc (⟨k + 2, by omega⟩ : Fin (k + 3)))} : Finset (Fin n)) := by
    rw [hπ₂_u, hπ₂_v, Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with hb | hb
    all_goals
      have h := congrArg Fin.val (π₁.injective hb)
      simp only [Fin.val_castSucc] at h
      omega
  have h01 : (⟨0, by omega⟩ : Fin (k + 3)) ≠ ⟨1, by omega⟩ := by
    intro h
    have h' := congrArg Fin.val h
    simp only at h'
    omega
  have hk12 : (⟨k + 1, by omega⟩ : Fin (k + 3)) ≠ ⟨k + 2, by omega⟩ := by
    intro h
    have h' := congrArg Fin.val h
    simp only at h'
    omega
  have hcomm := GGSecFiveBPermOmKFrame.normPerm_swap_commute_of_frames_of_join hBs hy₁ hX₁ hy₂
    hX₂ h𝒦 h₁ h₂ (by omega : 3 ≤ k + 3) (by omega : 3 ≤ k + 3) hn h01 hk12 hdisj
  let f : Equiv.Perm (Fin (k + 3)) →* G := κ₁.comp (normPerm E (by omega : 3 ≤ k + 3))
  let g : Equiv.Perm (Fin (k + 3)) →* G := κ₂.comp (normPerm E (by omega : 3 ≤ k + 3))
  have hCross : Commute (f (adjSwap (k + 2) 0)) (g (adjSwap (k + 2) (k + 1))) := by
    rw [adjSwap_of_lt (by omega : 0 < k + 2), adjSwap_of_lt (by omega : k + 1 < k + 2)]
    simpa only [f, g, MonoidHom.comp_apply] using hcomm
  exact exists_hom_perm_of_overlap (m := k) f g hOverlap hCross

end Crossing

end CFSG.StandardType

end
