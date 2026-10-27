module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModC2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenModBridge

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.Quasithin.F53Mod CFSG.Quasithin.F7 CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace EvenMod

theorem secIdx_le_secIdx {X L E F N : Subgroup G} (hNX : N ≤ X)
    (hL : X ≤ Subgroup.normalizer (L : Set G)) (hE : X ≤ Subgroup.normalizer (E : Set G))
    (hF : X ≤ Subgroup.normalizer (F : Set G)) (hLE : L ≤ E) (hEF : E ≤ F) (hFN : F ≤ N)
    {x : G} (hx : x ∈ X) :
    secIdx (Subgroup.zpowers x) E F ≤ secIdx (Subgroup.zpowers x) L N := by
  have h1 := secIdx_mul_le (x := x) (hLE.trans hEF) hFN (hNX.trans hL) (hNX.trans hF) (hL hx)
    (hF hx)
  have h2 := secIdx_mul_le (x := x) hLE hEF ((hFN.trans hNX).trans hL) ((hFN.trans hNX).trans hE)
    (hL hx) (hE hx)
  have h3 := secIdx_pos (Subgroup.zpowers x) F N
  have h4 := secIdx_pos (Subgroup.zpowers x) L E
  calc secIdx (Subgroup.zpowers x) E F
      ≤ secIdx (Subgroup.zpowers x) L E * secIdx (Subgroup.zpowers x) E F :=
        Nat.le_mul_of_pos_left _ h4
    _ ≤ secIdx (Subgroup.zpowers x) L F := h2
    _ ≤ secIdx (Subgroup.zpowers x) L F * secIdx (Subgroup.zpowers x) F N :=
        Nat.le_mul_of_pos_right _ h3
    _ ≤ _ := h1

omit [Finite G] in
theorem le_normalizer_of_isNormalIn {X U K : Subgroup G} (h : IsNormalIn X U K) :
    X ≤ Subgroup.normalizer (K : Set G) :=
  X1512.le_normalizer_of_forall h.2

theorem two_le_secIdx_of_noncentral {X U L N : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5))) (hU : U ≤ pCoreOf 2 X)
    (hstep : IsChiefStep X U L N) (hnc : ¬ IsCentralStep X L N) {x : G} (hx : x ∈ X)
    (hxQ : x ∉ pCoreOf 2 X) : 2 ≤ secIdx (Subgroup.zpowers x) L N := by
  have hcs : cSecIn X L N = pCoreOf 2 X := by
    rcases chief_central_or_nat_or_orth hq hU hstep with h | ⟨h, -⟩
    · exact absurd h hnc
    · exact h
  have hNX : N ≤ X := (hstep.1.1.trans hU).trans (pCoreOf_le 2 X)
  have hL := le_normalizer_of_isNormalIn hstep.2.1
  have hne : secIdx (Subgroup.zpowers x) L N ≠ 1 := by
    intro h1
    rw [secIdx_eq_one_iff (hNX.trans hL) (hL hx)] at h1
    exact hxQ (hcs ▸ (mem_cSecIn_iff hL).mpr ⟨hx, h1⟩)
  have hpos := secIdx_pos (Subgroup.zpowers x) L N
  omega

end EvenMod

theorem S11_chief_orth {X U L E F N : Subgroup G} (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hU : U ≤ pCoreOf 2 X) (hNU : N ≤ U) (hL : X ≤ Subgroup.normalizer (L : Set G))
    (hLE : L ≤ E) (hFN : F ≤ N)
    (hstep : IsChiefStep X U E F) (hnc : ¬ IsCentralStep X E F) {x : G} (hx : x ∈ X)
    (hxQ : x ∉ pCoreOf 2 X) (h2 : secIdx (Subgroup.zpowers x) L N ≤ 2) :
    IsOrthSec X E F ∧ secIdx (Subgroup.zpowers x) E F = 2 := by
  have hNX : N ≤ X := (hNU.trans hU).trans (pCoreOf_le 2 X)
  have hle : secIdx (Subgroup.zpowers x) E F ≤ 2 :=
    (EvenMod.secIdx_le_secIdx hNX hL (EvenMod.le_normalizer_of_isNormalIn hstep.2.1)
      (EvenMod.le_normalizer_of_isNormalIn hstep.1) hLE hstep.2.2.1.le hFN hx).trans h2
  have hge := EvenMod.two_le_secIdx_of_noncentral hq hU hstep hnc hx hxQ
  refine ⟨?_, le_antisymm hle hge⟩
  rcases chief_central_or_nat_or_orth hq hU hstep with h | ⟨hcs, hnat | horth⟩
  · exact absurd h hnc
  · have h4 := IsNatSec.four_le_secIdx hnat hstep.2.2.1.le hx (by rw [hcs]; exact hxQ)
    omega
  · exact horth

theorem S11_chief_not_two {X U L L₁ N₁ L₂ N₂ N : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5))) (hU : U ≤ pCoreOf 2 X) (hNU : N ≤ U)
    (hL : X ≤ Subgroup.normalizer (L : Set G)) (hLL₁ : L ≤ L₁) (hN₁L₂ : N₁ ≤ L₂) (hN₂N : N₂ ≤ N)
    (hs₁ : IsChiefStep X U L₁ N₁) (hs₂ : IsChiefStep X U L₂ N₂)
    (hc₁ : ¬ IsCentralStep X L₁ N₁) (hc₂ : ¬ IsCentralStep X L₂ N₂) {x : G} (hx : x ∈ X)
    (hxQ : x ∉ pCoreOf 2 X) (h2 : secIdx (Subgroup.zpowers x) L N ≤ 2) : False := by
  have hNX : N ≤ X := (hNU.trans hU).trans (pCoreOf_le 2 X)
  have hnL₁ := EvenMod.le_normalizer_of_isNormalIn hs₁.2.1
  have hnN₁ := EvenMod.le_normalizer_of_isNormalIn hs₁.1
  have hnL₂ := EvenMod.le_normalizer_of_isNormalIn hs₂.2.1
  have hnN₂ := EvenMod.le_normalizer_of_isNormalIn hs₂.1
  have hL₂N : L₂ ≤ N := hs₂.2.2.1.le.trans hN₂N
  have hsplit := secIdx_mul_le (x := x) (hLL₁.trans (hs₁.2.2.1.le.trans hN₁L₂)) hL₂N
    (hNX.trans hL) (hNX.trans hnL₂) (hL hx) (hnL₂ hx)
  have h1 : secIdx (Subgroup.zpowers x) L₁ N₁ ≤ secIdx (Subgroup.zpowers x) L L₂ :=
    EvenMod.secIdx_le_secIdx (hL₂N.trans hNX) hL hnL₁ hnN₁ hLL₁ hs₁.2.2.1.le hN₁L₂ hx
  have h2' : secIdx (Subgroup.zpowers x) L₂ N₂ ≤ secIdx (Subgroup.zpowers x) L₂ N :=
    EvenMod.secIdx_le_secIdx hNX hnL₂ hnL₂ hnN₂ le_rfl hs₂.2.2.1.le hN₂N hx
  have h3 := EvenMod.two_le_secIdx_of_noncentral hq hU hs₁ hc₁ hx hxQ
  have h4 := EvenMod.two_le_secIdx_of_noncentral hq hU hs₂ hc₂ hx hxQ
  have h5 : 4 ≤ secIdx (Subgroup.zpowers x) L L₂ * secIdx (Subgroup.zpowers x) L₂ N :=
    (Nat.mul_le_mul (h3.trans h1) (h4.trans h2'))
  omega

namespace EvenMod

omit [Finite G] in
theorem isSec_sq {X L N : Subgroup G} (hsec : IsSec X L N) (w : hsec.W) : w * w = 1 := by
  obtain ⟨y, rfl⟩ := hsec.proj_surjective w
  rw [← map_mul, hsec.proj_eq_one_iff]
  simpa [pow_two] using hsec.sq y y.2

omit [Finite G] in
theorem comm_mem_of_odd {X L N : Subgroup G} (hsec : IsSec X L N) {K : Subgroup G} {g : G}
    (hg : g ∈ X) {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1)
    (h1 : ∀ y ∈ N, g * y * g⁻¹ * y⁻¹ ∈ K) (h2 : ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ L) :
    ∀ y ∈ N, g * y * g⁻¹ * y⁻¹ ∈ L := by
  intro y hy
  set φ := hsec.conjHom ⟨g, hg⟩ with hφ
  have hφm : φ ^ m = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨g, hg⟩ : ↥X) ^ m = 1 := Subtype.ext (by simpa using hgm)
    rw [this, map_one]
  have hodd : Odd (orderOf φ) := hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hφm)
  have hδ : ∀ z : ↥N, delHom φ (hsec.proj z) = hsec.proj (hsec.conjN ⟨g, hg⟩ z * z⁻¹) := by
    intro z
    rw [delHom_apply, hφ, IsSec.conjHom_mk, map_mul, map_inv]
  have hc : ∀ z : ↥N, ((hsec.conjN ⟨g, hg⟩ z * z⁻¹ : ↥N) : G) = g * z * g⁻¹ * (z : G)⁻¹ := by
    intro z
    simp [IsSec.conjN]
  have hfix : φ (hsec.proj ⟨y, hy⟩) = hsec.proj ⟨y, hy⟩ := by
    refine eq_of_iterate_delHom_eq_one_of_odd (isSec_sq hsec) hodd (k := 2) ?_
    show delHom φ (delHom φ (hsec.proj ⟨y, hy⟩)) = 1
    rw [hδ ⟨y, hy⟩, hδ, hsec.proj_eq_one_iff, hc]
    exact h2 _ (by rw [hc]; exact h1 y hy)
  have h3 : hsec.proj (hsec.conjN ⟨g, hg⟩ ⟨y, hy⟩ * ⟨y, hy⟩⁻¹) = 1 := by
    rw [← hδ, delHom_apply, hfix, mul_inv_cancel]
  rw [hsec.proj_eq_one_iff, hc] at h3
  exact h3

end EvenMod

theorem comm_oTwoRes_le_of_central {X U L N : Subgroup G} (hsec : IsSec X L N) (hNU : N ≤ U)
    (hc : ∀ L' N' : Subgroup G, L ≤ L' → N' ≤ N → IsChiefStep X U L' N' →
      IsCentralStep X L' N') : ⁅N, oTwoRes X⁆ ≤ L := by
  suffices key : ∀ n : ℕ, ∀ N : Subgroup G, Nat.card N = n → IsSec X L N → N ≤ U →
      (∀ L' N' : Subgroup G, L ≤ L' → N' ≤ N → IsChiefStep X U L' N' →
        IsCentralStep X L' N') → oTwoRes X ≤ cSecIn X L N by
    have h := key _ N rfl hsec hNU hc
    rw [Subgroup.commutator_le]
    intro y hy l hl
    have h1 := ((mem_cSecIn_iff hsec.normL).mp (h hl)).2 y hy
    rw [show ⁅y, l⁆ = (l * y * l⁻¹ * y⁻¹)⁻¹ by simp only [commutatorElement_def]; group]
    exact L.inv_mem h1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hn hsec hNU hc
  by_cases hNL : N ≤ L
  · intro l hl
    rw [mem_cSecIn_iff hsec.normL]
    exact ⟨oTwoRes_le X hl, fun y hy =>
      L.mul_mem (hsec.conj_mem_L (oTwoRes_le X hl) (hNL hy)) (L.inv_mem (hNL hy))⟩
  · set S : Set (Subgroup G) := {K | IsNormalIn X U K ∧ L ≤ K ∧ K < N} with hS
    have hLS : L ∈ S := ⟨⟨hsec.le.trans hNU, fun g hg l hl => hsec.conj_mem_L hg hl⟩, le_rfl,
      lt_of_le_of_ne hsec.le fun h => hNL (h ▸ le_rfl)⟩
    obtain ⟨K, ⟨hKn, hLK, hKN⟩, hmax⟩ :=
      Set.exists_max_image S (fun K => Nat.card K) (Set.toFinite S) ⟨L, hLS⟩
    have hXK : X ≤ Subgroup.normalizer (K : Set G) := EvenMod.le_normalizer_of_isNormalIn hKn
    have hstep : IsChiefStep X U K N := by
      refine ⟨⟨hNU, fun g hg y hy => (Subgroup.mem_normalizer_iff.mp (hsec.normN hg) y).mp hy⟩,
        hKn, hKN, fun K' hK' hKK' hK'N => ?_⟩
      by_cases h : K' = N
      · exact Or.inr h
      · exact Or.inl (Subgroup.eq_of_le_of_card_ge hKK'
          (hmax K' ⟨hK', hLK.trans hKK', lt_of_le_of_ne hK'N h⟩)).symm
    have hcen : IsCentralStep X K N := hc K N hLK le_rfl hstep
    have hcardK : Nat.card K < n := by
      rw [← hn]
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hKN.le) fun h => hKN.ne ?_
      exact Subgroup.eq_of_le_of_card_ge hKN.le h.ge
    have hIH := ih _ hcardK K rfl (EvenMod.isSec_of_le hsec hLK hKN.le hXK) (hKN.le.trans hNU)
      fun L' N' h1 h2 h3 => hc L' N' h1 (h2.trans hKN.le) h3
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hgX, m, hm, hgm⟩
    rw [SetLike.mem_coe, mem_cSecIn_iff hsec.normL]
    refine ⟨hgX, EvenMod.comm_mem_of_odd hsec hgX hm hgm (fun y hy => hcen g hgX y hy) ?_⟩
    intro k hk
    have hg' : g ∈ oTwoRes X := Subgroup.subset_closure ⟨hgX, m, hm, hgm⟩
    exact ((mem_cSecIn_iff hsec.normL).mp (hIH hg')).2 k hk

theorem exists_noncentral_of_not_le {X U L N : Subgroup G} (hsec : IsSec X L N) (hNU : N ≤ U)
    (h : ¬ ⁅N, oTwoRes X⁆ ≤ L) :
    ∃ L' N' : Subgroup G, L ≤ L' ∧ N' ≤ N ∧ IsChiefStep X U L' N' ∧
      ¬ IsCentralStep X L' N' := by
  by_contra hcon
  push Not at hcon
  exact h (comm_oTwoRes_le_of_central hsec hNU fun L' N' h1 h2 h3 => hcon L' N' h1 h2 h3)

theorem S11_chief {X U L E F N : Subgroup G} (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5)))
    (hU : U ≤ pCoreOf 2 X) (hNU : N ≤ U) (hsec : IsSec X L N) (hLE : L ≤ E) (hFN : F ≤ N)
    (hstep : IsChiefStep X U E F) (hnc : ¬ IsCentralStep X E F) {x : G} (hx : x ∈ X)
    (hxQ : x ∉ pCoreOf 2 X) (h2 : secIdx (Subgroup.zpowers x) L N ≤ 2) :
    IsOrthSec X E F ∧ secIdx (Subgroup.zpowers x) E F = 2 ∧
      (∀ L' N' : Subgroup G, L ≤ L' → N' ≤ E → IsChiefStep X U L' N' →
        IsCentralStep X L' N') ∧
      (∀ L' N' : Subgroup G, F ≤ L' → N' ≤ N → IsChiefStep X U L' N' →
        IsCentralStep X L' N') ∧
      ⁅E, oTwoRes X⁆ ≤ L ∧ ⁅N, oTwoRes X⁆ ≤ F := by
  obtain ⟨horth, hidx⟩ := S11_chief_orth hq hU hNU hsec.normL hLE hFN hstep hnc hx hxQ h2
  have hEF : E < F := hstep.2.2.1
  have h3 : ∀ L' N' : Subgroup G, L ≤ L' → N' ≤ E → IsChiefStep X U L' N' →
      IsCentralStep X L' N' := fun L' N' h1 h1' hs => by
    by_contra hc'
    exact S11_chief_not_two hq hU hNU hsec.normL h1 h1' hFN hs hstep hc' hnc hx hxQ h2
  have h4 : ∀ L' N' : Subgroup G, F ≤ L' → N' ≤ N → IsChiefStep X U L' N' →
      IsCentralStep X L' N' := fun L' N' h1 h1' hs => by
    by_contra hc'
    exact S11_chief_not_two hq hU hNU hsec.normL hLE h1 h1' hstep hs hnc hc' hx hxQ h2
  have hEN : E ≤ N := hEF.le.trans hFN
  refine ⟨horth, hidx, h3, h4, ?_, ?_⟩
  · exact comm_oTwoRes_le_of_central
      (EvenMod.isSec_of_le hsec hLE hEN (EvenMod.le_normalizer_of_isNormalIn hstep.2.1))
      (hEN.trans hNU) h3
  · exact comm_oTwoRes_le_of_central
      (EvenMod.isSec_of_ge hsec (hLE.trans hEF.le) hFN
        (EvenMod.le_normalizer_of_isNormalIn hstep.1)) hNU h4

omit [Finite G] in
theorem comm_oTwoRes_le_trans {X L K N : Subgroup G} (hsec : IsSec X L N)
    (h1 : ⁅N, oTwoRes X⁆ ≤ K) (h2 : ⁅K, oTwoRes X⁆ ≤ L) : ⁅N, oTwoRes X⁆ ≤ L := by
  have hle : oTwoRes X ≤ cSecIn X L N := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hgX, m, hm, hgm⟩
    have hg' : g ∈ oTwoRes X := Subgroup.subset_closure ⟨hgX, m, hm, hgm⟩
    rw [SetLike.mem_coe, mem_cSecIn_iff hsec.normL]
    exact ⟨hgX, EvenMod.comm_mem_of_odd hsec hgX hm hgm
      (fun y hy => EvenMod.commutator_le_iff.mp h1 g hg' y hy)
      (fun k hk => EvenMod.commutator_le_iff.mp h2 g hg' k hk)⟩
  refine EvenMod.commutator_le_iff.mpr fun l hl y hy => ?_
  exact ((mem_cSecIn_iff hsec.normL).mp (hle hl)).2 y hy

end CFSG.Quasithin.F53.Stellmacher.S43.Even
