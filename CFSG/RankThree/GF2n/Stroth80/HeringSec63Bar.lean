module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

namespace HS6

section Bar

variable {G : Type} [Group G] (M Q : Subgroup G) [(Q.subgroupOf M).Normal]

@[expose] noncomputable def piM (g : G) : ↥M ⧸ Q.subgroupOf M := by
  classical
  exact if h : g ∈ M then QuotientGroup.mk ⟨g, h⟩ else 1

variable {M Q}

theorem piM_of_mem {g : G} (hg : g ∈ M) : piM M Q g = QuotientGroup.mk ⟨g, hg⟩ := by
  unfold piM
  exact dif_pos hg

theorem piM_mul {g h : G} (hg : g ∈ M) (hh : h ∈ M) :
    piM M Q (g * h) = piM M Q g * piM M Q h := by
  rw [piM_of_mem (M.mul_mem hg hh), piM_of_mem hg, piM_of_mem hh]
  rfl

theorem piM_inv {g : G} (hg : g ∈ M) : piM M Q g⁻¹ = (piM M Q g)⁻¹ := by
  rw [piM_of_mem (M.inv_mem hg), piM_of_mem hg]
  rfl

theorem piM_one : piM M Q (1 : G) = 1 := by
  rw [piM_of_mem M.one_mem]
  rfl

theorem piM_eq_iff {g h : G} (hg : g ∈ M) (hh : h ∈ M) :
    piM M Q g = piM M Q h ↔ g⁻¹ * h ∈ Q := by
  rw [piM_of_mem hg, piM_of_mem hh, QuotientGroup.eq]
  exact Subgroup.mem_subgroupOf

theorem piM_eq_one_iff {g : G} (hg : g ∈ M) : piM M Q g = 1 ↔ g ∈ Q := by
  rw [piM_of_mem hg, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf

theorem exists_piM (y : ↥M ⧸ Q.subgroupOf M) : ∃ g ∈ M, piM M Q g = y := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨x, x.2, piM_of_mem x.2⟩

theorem piM_conj {g h : G} (hg : g ∈ M) (hh : h ∈ M) :
    piM M Q (g * h * g⁻¹) = piM M Q g * piM M Q h * (piM M Q g)⁻¹ := by
  rw [piM_mul (M.mul_mem hg hh) (M.inv_mem hg), piM_mul hg hh, piM_inv hg]

theorem mem_bar {S : Subgroup G} (y : ↥M ⧸ Q.subgroupOf M) :
    y ∈ bar M Q S ↔ ∃ g ∈ S, g ∈ M ∧ piM M Q g = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, x.2, by rw [piM_of_mem x.2]; rfl⟩
  · rintro ⟨g, hgS, hgM, rfl⟩
    exact ⟨⟨g, hgM⟩, Subgroup.mem_subgroupOf.mpr hgS, by rw [piM_of_mem hgM]; rfl⟩

theorem piM_mem_bar {S : Subgroup G} {g : G} (hgS : g ∈ S) (hgM : g ∈ M) :
    piM M Q g ∈ bar M Q S := (mem_bar _).mpr ⟨g, hgS, hgM, rfl⟩

theorem bar_mono {S T : Subgroup G} (h : S ≤ T) : bar M Q S ≤ bar M Q T := fun y hy => by
  obtain ⟨g, hg, hgM, rfl⟩ := (mem_bar y).mp hy
  exact piM_mem_bar (h hg) hgM

theorem bar_eq_bot_of_le {S : Subgroup G} (hSQ : S ≤ Q) (hSM : S ≤ M) : bar M Q S = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨g, hg, hgM, rfl⟩ := (mem_bar y).mp hy
  rw [Subgroup.mem_bot, piM_eq_one_iff hgM]
  exact hSQ hg

theorem piM_mem_bar_iff {S : Subgroup G} (hQS : Q ≤ S) {g : G} (hgM : g ∈ M) :
    piM M Q g ∈ bar M Q S ↔ g ∈ S := by
  constructor
  · intro h
    obtain ⟨g', hg'S, hg'M, hg'⟩ := (mem_bar _).mp h
    have hq : g'⁻¹ * g ∈ Q := (piM_eq_iff hg'M hgM).mp hg'
    have : g = g' * (g'⁻¹ * g) := by group
    rw [this]
    exact S.mul_mem hg'S (hQS hq)
  · intro h
    exact piM_mem_bar h hgM

theorem piM_comm_of_comm_mem {g h : G} (hg : g ∈ M) (hh : h ∈ M) (hc : ⁅g, h⁆ ∈ Q) :
    piM M Q g * piM M Q h = piM M Q h * piM M Q g := by
  have hcM : ⁅g, h⁆ ∈ M := by
    simp only [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hg hh) (M.inv_mem hg)) (M.inv_mem hh)
  have h1 : piM M Q ⁅g, h⁆ = 1 := (piM_eq_one_iff hcM).mpr hc
  have h2 : piM M Q ⁅g, h⁆ = ⁅piM M Q g, piM M Q h⁆ := by
    simp only [commutatorElement_def]
    rw [piM_mul (M.mul_mem (M.mul_mem hg hh) (M.inv_mem hg)) (M.inv_mem hh),
      piM_mul (M.mul_mem hg hh) (M.inv_mem hg), piM_mul hg hh, piM_inv hg, piM_inv hh]
  rw [h2] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem bar_inf {S T : Subgroup G} (hQS : Q ≤ S) (hQT : Q ≤ T) :
    bar M Q (S ⊓ T) = bar M Q S ⊓ bar M Q T := by
  apply le_antisymm
  · exact le_inf (bar_mono inf_le_left) (bar_mono inf_le_right)
  · intro y hy
    obtain ⟨g, hgS, hgM, rfl⟩ := (mem_bar y).mp hy.1
    exact piM_mem_bar ⟨hgS, (piM_mem_bar_iff hQT hgM).mp hy.2⟩ hgM

theorem bar_injective {S T : Subgroup G} (hQS : Q ≤ S) (hQT : Q ≤ T) (hSM : S ≤ M)
    (hTM : T ≤ M) (h : bar M Q S = bar M Q T) : S = T := by
  apply le_antisymm
  · intro g hg
    have : piM M Q g ∈ bar M Q T := h ▸ piM_mem_bar hg (hSM hg)
    exact (piM_mem_bar_iff hQT (hSM hg)).mp this
  · intro g hg
    have : piM M Q g ∈ bar M Q S := h ▸ piM_mem_bar hg (hTM hg)
    exact (piM_mem_bar_iff hQS (hTM hg)).mp this

theorem conj_bar (hQM : Q ≤ M) {S : Subgroup G} {g : G} (hg : g ∈ M) :
    conjSubgroup (piM M Q g) (bar M Q S) = bar M Q (conjSubgroup g S) := by
  have hQ : ∀ x ∈ Q, ∀ k ∈ M, k * x * k⁻¹ ∈ Q := by
    intro x hx k hk
    have hn : (Q.subgroupOf M).Normal := inferInstance
    have := hn.conj_mem ⟨x, hQM hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨k, hk⟩
    exact Subgroup.mem_subgroupOf.mp this
  ext y
  obtain ⟨x, hxM, rfl⟩ := exists_piM y
  rw [mem_conjSubgroup, ← piM_inv hg, ← piM_mul (M.inv_mem hg) hxM,
    ← piM_mul (M.mul_mem (M.inv_mem hg) hxM) hg, mem_bar, mem_bar]
  constructor
  · rintro ⟨s, hsS, hsM, hs⟩
    refine ⟨g * s * g⁻¹, mem_conjSubgroup.mpr (by
      rw [show g⁻¹ * (g * s * g⁻¹) * g = s by group]; exact hsS),
      M.mul_mem (M.mul_mem hg hsM) (M.inv_mem hg), ?_⟩
    rw [piM_eq_iff (M.mul_mem (M.mul_mem hg hsM) (M.inv_mem hg)) hxM]
    have h1 : s⁻¹ * (g⁻¹ * x * g) ∈ Q := (piM_eq_iff hsM
      (M.mul_mem (M.mul_mem (M.inv_mem hg) hxM) hg)).mp hs
    have := hQ _ h1 g hg
    rwa [show g * (s⁻¹ * (g⁻¹ * x * g)) * g⁻¹ = (g * s * g⁻¹)⁻¹ * x by group] at this
  · rintro ⟨z, hzS, hzM, hz⟩
    refine ⟨g⁻¹ * z * g, mem_conjSubgroup.mp hzS, M.mul_mem (M.mul_mem (M.inv_mem hg) hzM) hg,
      ?_⟩
    rw [piM_eq_iff (M.mul_mem (M.mul_mem (M.inv_mem hg) hzM) hg)
      (M.mul_mem (M.mul_mem (M.inv_mem hg) hxM) hg)]
    have h1 : z⁻¹ * x ∈ Q := (piM_eq_iff hzM hxM).mp hz
    have := hQ _ h1 g⁻¹ (M.inv_mem hg)
    rwa [show g⁻¹ * (z⁻¹ * x) * g⁻¹⁻¹ = (g⁻¹ * z * g)⁻¹ * (g⁻¹ * x * g) by group] at this

theorem exists_lift_normalizer (hQM : Q ≤ M) (hQn : ∀ x ∈ Q, ∀ k ∈ M, k * x * k⁻¹ ∈ Q)
    {L : Subgroup G} (hQL : Q ≤ L) (hLM : L ≤ M) {ĥ : ↥M ⧸ Q.subgroupOf M}
    (hĥ : ĥ ∈ Subgroup.normalizer ((bar M Q L : Subgroup _) : Set _)) :
    ∃ h ∈ M, piM M Q h = ĥ ∧ conjSubgroup h L = L := by
  obtain ⟨h, hM, rfl⟩ := exists_piM ĥ
  refine ⟨h, hM, rfl, ?_⟩
  have h1 : conjSubgroup (piM M Q h) (bar M Q L) = bar M Q L := conjSubgroup_eq_self_iff.mpr hĥ
  rw [conj_bar hQM hM] at h1
  refine bar_injective ?_ hQL ?_ hLM h1
  · intro x hx
    rw [mem_conjSubgroup]
    have := hQn x hx h⁻¹ (M.inv_mem hM)
    rw [inv_inv] at this
    exact hQL this
  · intro y hy
    have hy' : h⁻¹ * y * h ∈ L := mem_conjSubgroup.mp hy
    have : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
    rw [this]
    exact M.mul_mem (M.mul_mem hM (hLM hy')) (M.inv_mem hM)

theorem piM_mem_normalizer (hQM : Q ≤ M) {L : Subgroup G} {h : G} (hM : h ∈ M)
    (hL : conjSubgroup h L = L) :
    piM M Q h ∈ Subgroup.normalizer ((bar M Q L : Subgroup _) : Set _) := by
  rw [← conjSubgroup_eq_self_iff, conj_bar hQM hM, hL]

theorem card_bar_mul {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M) :
    Nat.card (bar M Q S) * Nat.card Q = Nat.card S := by
  let f : ↥S →* bar M Q S :=
    ((QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hSM)).codRestrict (bar M Q S)
      (fun s => ⟨Subgroup.inclusion hSM s, Subgroup.mem_subgroupOf.mpr s.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hgS, hgM, rfl⟩ := (mem_bar y).mp hy
    exact ⟨⟨g, hgS⟩, Subtype.ext (by
      show QuotientGroup.mk (Subgroup.inclusion hSM ⟨g, hgS⟩) = piM M Q g
      rw [piM_of_mem hgM]; rfl)⟩
  have hker : f.ker = Q.subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : QuotientGroup.mk (Subgroup.inclusion hSM s) = (1 : ↥M ⧸ Q.subgroupOf M) :=
        congrArg Subtype.val h
      have := (QuotientGroup.eq_one_iff _).mp h1
      exact Subgroup.mem_subgroupOf.mp this
    · intro h
      apply Subtype.ext
      show QuotientGroup.mk (Subgroup.inclusion hSM s) = (1 : ↥M ⧸ Q.subgroupOf M)
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf S)
  have h3 : Nat.card (↥S ⧸ Q.subgroupOf S) = Nat.card (bar M Q S) := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have h2 : Nat.card (Q.subgroupOf S) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
  rw [h3, h2] at h1
  exact h1.symm

end Bar

end HS6

end CFSG.RankThree.GF2n.Stroth80
