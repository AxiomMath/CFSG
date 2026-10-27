module

public import CFSG.Quasithin.EmptyFaithful.SBc2SzCore
public import CFSG.Quasithin.EmptyFaithful.S153DGen2
public import CFSG.Quasithin.SteinbergBSResidualCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc2

structure SzLift {G : Type} [Group G] (L P : Subgroup G) : Prop where
  card3 : ¬ 3 ∣ Nat.card ↥L
  maximal : ∀ W : Subgroup G, W ≤ L → L ⊓ Subgroup.normalizer (P : Set G) ≤ W →
    W = L ⊓ Subgroup.normalizer (P : Set G) ∨ W = L
  cent : ∀ x ∈ L, (∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ centerOf L) → x ∈ P
  solv : ∀ H : Subgroup G, H ≤ L → Group.IsSolvable ↥H → P ≤ H → H ≤ Subgroup.normalizer (P : Set G)
  yLemma : ∀ y : G, y ∈ Subgroup.normalizer (L : Set G) → y ^ 3 = 1 →
    (∀ b ∈ L ⊓ Subgroup.normalizer (P : Set G), b * y * b⁻¹ * y⁻¹ ∈ P) →
      y ∈ Subgroup.centralizer (L : Set G)

section Lift

variable {G : Type} [Group G] [Finite G] {L P : Subgroup G}

omit [Finite G] in
theorem mem_centerOf_iff_center {z : ↥L} :
    (z : G) ∈ centerOf L ↔ z ∈ Subgroup.center ↥L := by
  rw [centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, h⟩ g
    exact Subtype.ext (h g g.2)
  · intro h
    refine ⟨z.2, fun g hg => ?_⟩
    have := congrArg Subtype.val (h ⟨g, hg⟩)
    exact this

omit [Finite G] in
theorem mem_normalizer_subgroupOf_iff (hPL : P ≤ L) (l : ↥L) :
    l ∈ Subgroup.normalizer ((P.subgroupOf L : Subgroup ↥L) : Set ↥L) ↔
      (l : G) ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    constructor
    · intro hg
      have := (h ⟨g, hPL hg⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
      exact Subgroup.mem_subgroupOf.mp this
    · intro hg
      have hgL : g ∈ L := by
        have h1 : (l : G) * g * (l : G)⁻¹ ∈ L := hPL hg
        have h2 : (l : G)⁻¹ * ((l : G) * g * (l : G)⁻¹) * (l : G) ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem l.2) h1) l.2
        simpa [mul_assoc] using h2
      have := (h ⟨g, hgL⟩).mpr (Subgroup.mem_subgroupOf.mpr hg)
      exact Subgroup.mem_subgroupOf.mp this
  · intro h g
    have := h g
    simpa [Subgroup.mem_subgroupOf] using this

theorem szLift_of_facts (hq : CFSG.IsQuasisimple ↥L) (hPL : P ≤ L)
    (hZP : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ P) (hP2 : IsPGroup 2 P)
    {T : Subgroup (↥L ⧸ Subgroup.center ↥L)}
    (hT : T = (P.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))
    (hf : SzBorelFacts (↥L ⧸ Subgroup.center ↥L) T) : SzLift L P := by
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  set P' : Subgroup ↥L := P.subgroupOf L with hP'
  have hZP' : Z ≤ P' := fun z hz => Subgroup.mem_subgroupOf.mpr (hZP z hz)
  have hTcomap : T.comap π = P' := by
    rw [hT]
    exact Subgroup.comap_map_eq_self (by rw [hker]; exact hZP')
  have hNcomap : (Subgroup.normalizer (T : Set (↥L ⧸ Z))).comap π =
      Subgroup.normalizer (P' : Set ↥L) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective T hsurj, hTcomap]
  have hP'N : P' ≤ Subgroup.normalizer (P' : Set ↥L) := Subgroup.le_normalizer
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hdvd
    have hcard : Nat.card ↥L = Nat.card (↥L ⧸ Z) * Nat.card Z :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [hcard] at hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h | h
    · exact hf.card3 h
    · have hP'2 : IsPGroup 2 P' := A4.isPGroup_subgroupOf_of_le hPL hP2
      obtain ⟨n, hn⟩ := hP'2.exists_card_eq
      have h1 : Nat.card Z ∣ Nat.card P' := Subgroup.card_dvd_of_le hZP'
      rw [hn] at h1
      have h2 : 3 ∣ 2 ^ n := h.trans h1
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
      omega
  ·
    intro W hWL hBW
    set W' : Subgroup ↥L := W.subgroupOf L with hW'
    have hBW' : Subgroup.normalizer (P' : Set ↥L) ≤ W' := by
      intro l hl
      rw [Subgroup.mem_subgroupOf]
      exact hBW ⟨l.2, (mem_normalizer_subgroupOf_iff hPL l).mp hl⟩
    have hkerW : π.ker ≤ W' := by
      rw [hker]
      exact hZP'.trans (hP'N.trans hBW')
    have hmap : Subgroup.normalizer (T : Set (↥L ⧸ Z)) ≤ W'.map π := by
      intro x hx
      obtain ⟨l, rfl⟩ := hsurj x
      have : l ∈ Subgroup.normalizer (P' : Set ↥L) := by rw [← hNcomap]; exact hx
      exact ⟨l, hBW' this, rfl⟩
    have hW'eq : W' = (W'.map π).comap π := (Subgroup.comap_map_eq_self hkerW).symm
    rcases eq_or_lt_of_le hmap with h | h
    · left
      refine le_antisymm (fun w hw => ?_) hBW
      have hw' : (⟨w, hWL hw⟩ : ↥L) ∈ W' := Subgroup.mem_subgroupOf.mpr hw
      rw [hW'eq, ← h, hNcomap] at hw'
      exact ⟨hWL hw, (mem_normalizer_subgroupOf_iff hPL _).mp hw'⟩
    · right
      have htop := hf.coatom.2 _ h
      refine le_antisymm hWL fun l hl => ?_
      have : (⟨l, hl⟩ : ↥L) ∈ W' := by rw [hW'eq, htop]; exact Subgroup.mem_comap.mpr trivial
      exact Subgroup.mem_subgroupOf.mp this
  ·
    intro x hx hcomm
    have hxπ : π ⟨x, hx⟩ ∈ Subgroup.centralizer (T : Set (↥L ⧸ Z)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rw [hT] at ht
      obtain ⟨p', hp', rfl⟩ := ht
      have hc : (⟨x, hx⟩ * p' * ⟨x, hx⟩⁻¹ * p'⁻¹ : ↥L) ∈ Z := by
        have := hcomm (p' : G) (Subgroup.mem_subgroupOf.mp hp')
        exact mem_centerOf_iff_center.mp this
      have hπc : π (⟨x, hx⟩ * p' * ⟨x, hx⟩⁻¹ * p'⁻¹) = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact hc
      have key : π (⟨x, hx⟩ * p') = π (p' * ⟨x, hx⟩) := by
        have e : (⟨x, hx⟩ * p' : ↥L) =
            (⟨x, hx⟩ * p' * ⟨x, hx⟩⁻¹ * p'⁻¹) * (p' * ⟨x, hx⟩) := by group
        rw [e, map_mul, hπc, one_mul]
      rw [← map_mul, ← map_mul]
      exact key.symm
    have hxT : π ⟨x, hx⟩ ∈ T := hf.cent hxπ
    have : (⟨x, hx⟩ : ↥L) ∈ T.comap π := hxT
    rw [hTcomap] at this
    exact Subgroup.mem_subgroupOf.mp this
  ·
    intro H hHL hHs hPH
    set H' : Subgroup ↥L := H.subgroupOf L with hH'
    have hH's : Group.IsSolvable ↥H' :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hHL).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hHL).symm.surjective
    have hmapsolv : Group.IsSolvable ↥(H'.map π) :=
      Group.isSolvable_of_surjective (f := π.subgroupMap H') (π.subgroupMap_surjective H')
    have hle : T ≤ H'.map π := by
      rw [hT]
      exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
        (hPH (Subgroup.mem_subgroupOf.mp hx))
    have h1 := hf.solv _ hmapsolv hle
    intro h hh
    have hh' : (⟨h, hHL hh⟩ : ↥L) ∈ H' := Subgroup.mem_subgroupOf.mpr hh
    have : π ⟨h, hHL hh⟩ ∈ Subgroup.normalizer (T : Set (↥L ⧸ Z)) := h1 ⟨_, hh', rfl⟩
    have : (⟨h, hHL hh⟩ : ↥L) ∈ Subgroup.normalizer (P' : Set ↥L) := by
      rw [← hNcomap]; exact this
    exact (mem_normalizer_subgroupOf_iff hPL _).mp this
  ·
    intro y hyL hy3 hyc
    have hchar : Z.Characteristic := inferInstance
    set α : MulAut (↥L ⧸ Z) := SteinbergBS.conjQuotientHom L Z ⟨y, hyL⟩ with hα
    have hα3 : α * α * α = 1 := by
      have hyN3 : (⟨y, hyL⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hy3)
      have h := congrArg (SteinbergBS.conjQuotientHom L Z) hyN3
      rw [map_pow, map_one, pow_three'] at h
      exact h
    have hαl : ∀ l : ↥L, α (π l) = π (Subgroup.normalizerMonoidHom L ⟨y, hyL⟩ l) := fun l => rfl
    have hαcoe : ∀ l : ↥L,
        ((Subgroup.normalizerMonoidHom L ⟨y, hyL⟩ l : ↥L) : G) = y * l * y⁻¹ := fun l =>
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨y, hyL⟩ l
    have hcommα : ∀ b ∈ Subgroup.normalizer (T : Set (↥L ⧸ Z)), b⁻¹ * α b ∈ T := by
      intro b hb
      obtain ⟨l, rfl⟩ := hsurj b
      have hl : l ∈ Subgroup.normalizer (P' : Set ↥L) := by rw [← hNcomap]; exact hb
      have hlN : (l : G) ∈ Subgroup.normalizer (P : Set G) :=
        (mem_normalizer_subgroupOf_iff hPL l).mp hl
      have hlB : (l : G) ∈ L ⊓ Subgroup.normalizer (P : Set G) := ⟨l.2, hlN⟩
      have hlinv : (l : G)⁻¹ ∈ L ⊓ Subgroup.normalizer (P : Set G) :=
        (L ⊓ Subgroup.normalizer (P : Set G)).inv_mem hlB
      have h1 := hyc _ hlinv
      rw [hαl, ← map_inv, ← map_mul]
      rw [hT]
      refine ⟨l⁻¹ * Subgroup.normalizerMonoidHom L ⟨y, hyL⟩ l, ?_, rfl⟩
      rw [hP', SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, hαcoe,
        InvMemClass.coe_inv]
      simpa [mul_assoc] using h1
    have hα1 : α = 1 := hf.core α hα3 hcommα
    have hyCq : y ∈ SteinbergBS.quotientCentralizer (⊤ : Subgroup G) L Z := by
      rw [SteinbergBS.mem_quotientCentralizer_iff]
      refine ⟨Subgroup.mem_top _, hyL, fun l hl => ?_⟩
      have h := congrArg (fun f : MulAut (↥L ⧸ Z) => f (π ⟨l, hl⟩)) hα1
      simp only [MulAut.one_apply] at h
      rw [hαl, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem] at h
      refine ⟨_, h, ?_⟩
      simp [hαcoe, div_eq_mul_inv]
    have hle : ⁅L, SteinbergBS.quotientCentralizer (⊤ : Subgroup G) L Z⁆ ≤
        Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.commutator_le]
      intro l hl x hx
      rw [SteinbergBS.mem_quotientCentralizer_iff] at hx
      obtain ⟨-, -, hx3⟩ := hx
      have hxl := hx3 l hl
      have hmem : ⁅l, x⁆ ∈ Z.map L.subtype := by
        have := (Z.map L.subtype).inv_mem hxl
        have e : ⁅l, x⁆ = (x * l * x⁻¹ * l⁻¹)⁻¹ := by
          simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact this
      obtain ⟨z, hz, hzeq⟩ := hmem
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
      rw [← hzeq]
      exact congrArg Subtype.val this
    have hbot := S153D.commutator_eq_bot_of_quasisimple hq hle
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hm : ⁅l, y⁆ ∈ ⁅L, SteinbergBS.quotientCentralizer (⊤ : Subgroup G) L Z⁆ :=
      Subgroup.commutator_mem_commutator hl hyCq
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hm

theorem szLift_of_isSz
    (hq : CFSG.IsQuasisimple ↥L) (hZ : centerOf L = pCoreOf 2 L)
    (hsz : ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) (hP : IsSylowTwoOf P L) : SzLift L P := by
  obtain ⟨e, he⟩ := hsz
  have hPL : P ≤ L := hP.1
  have hZP : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ P := by
    intro z hz
    have h1 : (z : G) ∈ centerOf L := mem_centerOf_iff_center.mpr hz
    rw [hZ] at h1
    exact QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hP h1
  have hP2 : IsPGroup 2 P := hP.2.1
  let Tsyl : Sylow 2 (↥L ⧸ Subgroup.center ↥L) :=
    (A4.toSylow hP).mapSurjective (QuotientGroup.mk'_surjective _)
  have hT : (Tsyl : Subgroup (↥L ⧸ Subgroup.center ↥L)) =
      (P.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
    rw [Sylow.coe_mapSurjective, A4.toSylow_coe]
  exact szLift_of_facts hq hPL hZP hP2 hT (hT ▸ szBorelFacts_of_isSz he Tsyl)

end Lift

end SBc2

end CFSG.Quasithin
