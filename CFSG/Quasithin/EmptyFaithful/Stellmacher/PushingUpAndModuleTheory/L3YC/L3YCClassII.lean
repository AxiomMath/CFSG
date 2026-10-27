module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCClassIIAbs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCCommPhiCase4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.CaseFourCover

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.SBd7
open scoped commutatorElement

namespace Stellmacher.PU.L3YC

section Center

variable {B : Type} [Group B]

theorem central_of_center_card_two (V : Subgroup B) [V.Normal]
    (hc : Nat.card (Subgroup.center ↥V) = 2) (z : B)
    (hz : z ∈ (Subgroup.center ↥V).map V.subtype) (b : B) : b * z * b⁻¹ = z := by
  set Zs : Subgroup B := (Subgroup.center ↥V).map V.subtype with hZs
  have hcard : Nat.card Zs = 2 := by
    rw [hZs, Subgroup.card_map_of_injective V.subtype_injective, hc]
  have hconj : ∀ (b z : B), z ∈ Zs → b * z * b⁻¹ ∈ Zs := by
    intro b z hz
    obtain ⟨v, hv, rfl⟩ := hz
    have hvV : b * (v : B) * b⁻¹ ∈ V := Subgroup.Normal.conj_mem ‹_› _ v.2 b
    refine ⟨⟨_, hvV⟩, ?_, rfl⟩
    show _ ∈ Subgroup.center ↥V
    rw [Subgroup.mem_center_iff]
    rintro ⟨w, hw⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hw' : b⁻¹ * w * b ∈ V := by
      simpa using Subgroup.Normal.conj_mem ‹_› w hw b⁻¹
    have hcen := Subgroup.mem_center_iff.mp hv ⟨_, hw'⟩
    have hcen' : (b⁻¹ * w * b) * (v : B) = (v : B) * (b⁻¹ * w * b) := congrArg Subtype.val hcen
    calc w * (b * (v : B) * b⁻¹) = b * ((b⁻¹ * w * b) * (v : B)) * b⁻¹ := by group
      _ = b * ((v : B) * (b⁻¹ * w * b)) * b⁻¹ := by rw [hcen']
      _ = b * (v : B) * b⁻¹ * w := by group
  by_cases hz1 : z = 1
  · simp [hz1]
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.mp hcard
  have hall : ∀ u : Zs, u = x ∨ u = y := fun u => by
    have : u ∈ ({x, y} : Set Zs) := by rw [hset]; exact Set.mem_univ u
    simpa using this
  let z' : Zs := ⟨z, hz⟩
  let w' : Zs := ⟨b * z * b⁻¹, hconj b z hz⟩
  have hz1' : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hw1' : w' ≠ 1 := fun h => hz1 (by
    have h2 : b * z * b⁻¹ = 1 := congrArg Subtype.val h
    have h3 : z = b⁻¹ * (b * z * b⁻¹) * b := by group
    rw [h3, h2]; group)
  have : w' = z' := by
    rcases hall z' with h1 | h1 <;> rcases hall w' with h2 | h2 <;> rcases hall 1 with h3 | h3 <;>
      simp_all
  exact congrArg Subtype.val this

end Center

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nonempty_quot_equiv_gl {L : Subgroup G} (hq : IsLnTwoQuot L 3) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* GL (Fin 3) (ZMod 2)) := by
  obtain ⟨e⟩ := hq
  have hF : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  have htop := statedSL_eq_top_of_card_two hF 3
  exact ⟨e.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)⟩

theorem commutator_pCore_le_subgroupOf {G₀ R L : Subgroup G} (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (h : MS93.IsC134Case4Corr G₀ R L) :
    ⁅CFSG.pCore 2 ↥L, (⊤ : Subgroup ↥L)⁆ ≤ (c134Q G₀ L).subgroupOf L := by
  have hcomm := Stellmacher.CD.L3YC.comm_self_of_case4Corr h
  have hQeq : c134Q G₀ L = ⁅pCoreOf 2 L, L⁆ := by
    have := Stellmacher.CD.L3YC.c134Q_eq_of_comm_self (L := L) (S := G₀) hGL
      (by rwa [sup_eq_right.mpr hLG])
    rwa [sup_eq_right.mpr hLG] at this
  rw [hQeq, Subgroup.commutator_le]
  intro n hn g _
  have hn' : (n : G) ∈ pCoreOf 2 L := by
    unfold pCoreOf; exact ⟨n, hn, rfl⟩
  have hm := Subgroup.commutator_mem_commutator hn' g.2
  show ((⁅n, g⁆ : ↥L) : G) ∈ (⁅pCoreOf 2 L, L⁆ : Subgroup G)
  simpa [commutatorElement_def] using hm

theorem card_pCore_le_two_mul_map_c134Q
    {G₀ R L : Subgroup G} (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3) (hperf : ⁅L, L⁆ = L)
    (h : MS93.IsC134Case4Corr G₀ R L) {B : Type} [Group B] [Finite B] (π : ↥L →* B)
    (hπ : Function.Surjective π) (hK : IsPGroup 2 π.ker) :
    Nat.card (CFSG.pCore 2 B) ≤ 2 * Nat.card (((c134Q G₀ L).subgroupOf L).map π) ∧
      ((c134Q G₀ L).subgroupOf L).map π ≤ CFSG.pCore 2 B := by
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨e⟩ := nonempty_quot_equiv_gl hq
  have hQO : c134Q G₀ L ≤ pCoreOf 2 L := MS93.commutator_le_pCoreOf hLG hGL
  have hQN : (c134Q G₀ L).subgroupOf L ≤ CFSG.pCore 2 ↥L := by
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 L := hQO hx
    unfold pCoreOf at hx'
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hpN : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  have hQle := commutator_pCore_le_subgroupOf hLG hGL h
  refine ⟨?_, ?_⟩
  · calc Nat.card (CFSG.pCore 2 B) ≤ Nat.card ((CFSG.pCore 2 ↥L).map π) :=
          Subgroup.card_le_of_le (pCore_le_map π hπ hK)
      _ ≤ 2 * Nat.card (⁅CFSG.pCore 2 ↥L, (⊤ : Subgroup ↥L)⁆.map π) :=
          card_map_pCore_le π hK e
      _ ≤ 2 * Nat.card (((c134Q G₀ L).subgroupOf L).map π) :=
          Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le (Subgroup.map_mono hQle))
  · exact (Subgroup.map_mono hQN).trans (map_le_pCore π hπ _ hpN)

theorem classII_false
    {G₀ R L : Subgroup G} (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3) (hperf : ⁅L, L⁆ = L)
    (h : MS93.IsC134Case4Corr G₀ R L) {B : Type} [Group B] [Finite B] (π : ↥L →* B)
    (hπ : Function.Surjective π) (hK : IsPGroup 2 π.ker)
    (hV : CFSG.IsExtraspecial 2 ↥(CFSG.pCore 2 B)) (hV7 : Nat.card (CFSG.pCore 2 B) = 2 ^ 7) :
    False := by
  classical
  have hT1 := comm_frattini_eq_CQ hLG hGL hq h
  have hcomm := Stellmacher.CD.L3YC.comm_self_of_case4Corr h
  have hQeq : c134Q G₀ L = ⁅pCoreOf 2 L, L⁆ := by
    have := Stellmacher.CD.L3YC.c134Q_eq_of_comm_self (L := L) (S := G₀) hGL
      (by rwa [sup_eq_right.mpr hLG])
    rwa [sup_eq_right.mpr hLG] at this
  obtain ⟨⟨n, F, iF, fF, α, hFc, hα, hE2, hZ, hCU, hnatU, hnatΦ, -, hnatQ⟩, -⟩ := h
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨e⟩ := nonempty_quot_equiv_gl hq
  obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_map_commutator π hπ hK e hV hV7
  set Q := c134Q G₀ L with hQdef
  set Φ := frattiniIn Q with hΦdef
  set Zq := centerOf Q with hZqdef
  set C := c134CQ G₀ L with hCdef
  set U : Subgroup G := ⁅Zq, L⁆ with hUdef
  set Vb := CFSG.pCore 2 B with hVb
  have hQO : Q ≤ pCoreOf 2 L := MS93.commutator_le_pCoreOf hLG hGL
  have hQL : Q ≤ L := hQO.trans (pCoreOf_le 2 L)
  have hΦQ : Φ ≤ Q := Subgroup.map_subtype_le _
  have hZΦ : Zq ≤ Φ := hnatΦ.2.1
  have hUZ : U ≤ Zq := by rw [hZ]; exact le_sup_right
  have hpc : ∀ x : G, x ∈ pCoreOf 2 L → ∃ y ∈ CFSG.pCore 2 ↥L, (y : G) = x := by
    intro x hx
    unfold pCoreOf at hx
    exact Subgroup.mem_map.mp hx
  have hpN : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  have hπN : (CFSG.pCore 2 ↥L).map π ≤ Vb := map_le_pCore π hπ _ hpN
  let ρ : ↥Q →* B := π.comp (Subgroup.inclusion hQL)
  have hρV : ∀ y : ↥Q, ρ y ∈ Vb := by
    intro y
    obtain ⟨z, hz, hzy⟩ := hpc _ (hQO y.2)
    have : Subgroup.inclusion hQL y = z := Subtype.ext hzy.symm
    show π (Subgroup.inclusion hQL y) ∈ Vb
    rw [this]
    exact hπN ⟨z, hz, rfl⟩
  have hQp : IsPGroup 2 ↥Q := (pCoreOf_isPGroup 2 L).to_le hQO
  have hfr := frattini_le_comap_center hQp Vb ρ hρV
  have hNQ : ∀ x : ↥L, x ∈ ⁅CFSG.pCore 2 ↥L, (⊤ : Subgroup ↥L)⁆ → (x : G) ∈ Q := by
    intro x hx
    rw [hQeq]
    have hle : ⁅CFSG.pCore 2 ↥L, (⊤ : Subgroup ↥L)⁆ ≤ (⁅pCoreOf 2 L, L⁆).comap L.subtype := by
      rw [Subgroup.commutator_le]
      intro n hn g _
      have hn' : (n : G) ∈ pCoreOf 2 L := by
        unfold pCoreOf; exact ⟨n, hn, rfl⟩
      have hm := Subgroup.commutator_mem_commutator hn' g.2
      show ((⁅n, g⁆ : ↥L) : G) ∈ (⁅pCoreOf 2 L, L⁆ : Subgroup G)
      simpa [commutatorElement_def] using hm
    exact hle hx
  have hnotriv : ¬ ∀ y ∈ frattini ↥Q, ρ y = 1 := by
    intro hall
    exact hab (comm_of_frattini_trivial hQp ρ hall ⟨(a : G), hNQ a ha⟩ ⟨(b : G), hNQ b hb⟩)
  apply hnotriv
  let Dg : Subgroup G := π.ker.map L.subtype
  have hDg : ∀ (x : G) (hx : x ∈ L), π ⟨x, hx⟩ = 1 → x ∈ Dg := fun x hx h1 =>
    ⟨⟨x, hx⟩, h1, rfl⟩
  have hDg' : ∀ x ∈ Dg, ∃ hx : x ∈ L, π ⟨x, hx⟩ = 1 := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  have hcen : ∀ z ∈ (Subgroup.center ↥Vb).map Vb.subtype, ∀ c : B, c * z * c⁻¹ = z :=
    fun z hz c => central_of_center_card_two Vb (CFSG.IsExtraspecial.center_order_p 2 _) z hz c
  have hΦZ : ∀ x ∈ Φ, ∃ hx : x ∈ L, π ⟨x, hx⟩ ∈ (Subgroup.center ↥Vb).map Vb.subtype := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy' := hfr hy
    exact ⟨hQL y.2, ⟨ρ.codRestrict Vb hρV y, hy', rfl⟩⟩
  have hDgc : ∀ (x w : G) (hx : x ∈ L) (hw : w ∈ L),
      (∀ c : B, c * π ⟨x, hx⟩ * c⁻¹ = π ⟨x, hx⟩) → ⁅x, w⁆ ∈ Dg := by
    intro x w hx hw hc
    have hl : ⁅x, w⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem hx hw) (L.inv_mem hx)) (L.inv_mem hw)
    refine hDg _ hl ?_
    have : (⟨⁅x, w⁆, hl⟩ : ↥L) = ⁅(⟨x, hx⟩ : ↥L), (⟨w, hw⟩ : ↥L)⁆ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [this, map_commutatorElement, commutatorElement_def]
    have h2 := hc (π ⟨w, hw⟩)
    have e : π ⟨x, hx⟩ * π ⟨w, hw⟩ * (π ⟨x, hx⟩)⁻¹ * (π ⟨w, hw⟩)⁻¹ =
        (π ⟨w, hw⟩ * π ⟨x, hx⟩ * (π ⟨w, hw⟩)⁻¹ * (π ⟨x, hx⟩)⁻¹)⁻¹ := by group
    rw [e, h2]
    simp
  have hDgc' : ∀ (x w : G) (hx : x ∈ L) (hw : w ∈ L),
      (∀ c : B, c * π ⟨w, hw⟩ * c⁻¹ = π ⟨w, hw⟩) → ⁅x, w⁆ ∈ Dg := by
    intro x w hx hw hc
    have hl : ⁅x, w⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem hx hw) (L.inv_mem hx)) (L.inv_mem hw)
    refine hDg _ hl ?_
    have : (⟨⁅x, w⁆, hl⟩ : ↥L) = ⁅(⟨x, hx⟩ : ↥L), (⟨w, hw⟩ : ↥L)⁆ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [this, map_commutatorElement, commutatorElement_def]
    have h2 := hc (π ⟨x, hx⟩)
    have e : π ⟨x, hx⟩ * π ⟨w, hw⟩ * (π ⟨x, hx⟩)⁻¹ * (π ⟨w, hw⟩)⁻¹ =
        (π ⟨x, hx⟩ * π ⟨w, hw⟩ * (π ⟨x, hx⟩)⁻¹) * (π ⟨w, hw⟩)⁻¹ := by group
    rw [h2]
    simp
  have hΦL : ⁅Φ, L⁆ ≤ Dg := by
    refine Subgroup.commutator_le.mpr fun x hx w hw => ?_
    obtain ⟨hxL, hxZ⟩ := hΦZ x hx
    exact hDgc x w hxL hw (fun c => hcen _ hxZ c)
  have hQΦ : ⁅Q, Φ⁆ ≤ Dg := by
    refine Subgroup.commutator_le.mpr fun a ha x hx => ?_
    obtain ⟨hxL, hxZ⟩ := hΦZ x hx
    exact hDgc' a x (hQL ha) hxL (fun c => hcen _ hxZ c)
  have hCD : C ≤ Dg := hT1 ▸ hQΦ
  have hUU : ⁅U, L⁆ ⊔ ⊥ = U := Stellmacher.CD.L3YC.commutator_sup_eq hα.1 hnatU
  have hUD : U ≤ Dg := by
    calc U = ⁅U, L⁆ := by simpa using hUU.symm
      _ ≤ ⁅Φ, L⁆ := Subgroup.commutator_mono (hUZ.trans hZΦ) le_rfl
      _ ≤ Dg := hΦL
  have hZD : Zq ≤ Dg := by
    rw [hZ]
    exact sup_le hCD hUD
  have hΦD : Φ ≤ Dg := by
    have := Stellmacher.CD.L3YC.commutator_sup_eq hα.1 hnatΦ
    rw [← this]
    exact sup_le hΦL hZD
  intro y hy
  have hyΦ : (y : G) ∈ Φ := ⟨y, hy, rfl⟩
  exact (hDg' _ (hΦD hyΦ)).2

end Main

end Stellmacher.PU.L3YC

end CFSG.Quasithin
