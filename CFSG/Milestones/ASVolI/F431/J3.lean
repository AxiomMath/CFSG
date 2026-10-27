module

public import CFSG.Milestones.ASVolI.F4TISets

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section OTwoRes

theorem burnsideF4j_oTwoRes_map {A B : Type} [Group A] [Group B] (φ : A →* B)
    (hφ : Function.Injective φ) (X : Subgroup A) : oTwoRes (X.map φ) = (oTwoRes X).map φ := by
  unfold oTwoRes
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, m, hm, hym⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, ⟨hx, m, hm, hφ (by rw [map_pow, hym, map_one])⟩, rfl⟩
  · rintro ⟨x, ⟨hx, m, hm, hxm⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem φ hx, m, hm, by rw [← map_pow, hxm, map_one]⟩

theorem burnsideF4j_oTwoRes_subImg {Mb G : Type} [Group Mb] [Group G] {N : Subgroup Mb}
    (b : ↥N →* G) (hb : Function.Injective b) {X : Subgroup Mb} (hX : X ≤ N) :
    oTwoRes (subImg b X) = subImg b (oTwoRes X) := by
  unfold subImg
  rw [burnsideF4j_oTwoRes_map b hb]
  congr 1
  have h1 : oTwoRes X = (oTwoRes (X.subgroupOf N)).map N.subtype := by
    rw [← burnsideF4j_oTwoRes_map N.subtype N.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hX]
  rw [h1, CFSG.Quasithin.H13.F431.L3.subgroupOf_map_subtype_self]

theorem burnsideF4j_oTwoRes_mono {G : Type} [Group G] {X Y : Subgroup G} (h : X ≤ Y) :
    oTwoRes X ≤ oTwoRes Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

end OTwoRes

section Generic

theorem burnsideF4j_le_pCoreOf_of_twoClosed {G : Type} [Group G] [Finite G]
    {H X X' V : Subgroup G} (hX : X ≤ H) (hX' : X' ≤ H)
    (hH : IsSylowTwoOf (pCoreOf 2 (oTwoRes H)) (oTwoRes H)) (hVp : IsPGroup 2 V)
    (hVX : V ≤ oTwoRes X) (hVX' : V ≤ X') : V ≤ pCoreOf 2 X' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 (oTwoRes H)
  have hVH : V ≤ oTwoRes H := hVX.trans (burnsideF4j_oTwoRes_mono hX)
  have hVP : V ≤ P := by
    obtain ⟨c, hc, hle⟩ := F7.isSylowTwoOf_exists_conj_le hH hVH hVp
    have hcN : c ∈ Subgroup.normalizer (P : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (oTwoRes H) hc
    have : conjSub c P = P := CFSG.Quasithin.H13.F431.L3.conjSub_eq_of_mem_normalizer hcN
    rwa [this] at hle
  have hHN : H ≤ Subgroup.normalizer (P : Set G) :=
    (le_normalizer_oTwoRes H).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hPX' : P ⊓ X' ≤ pCoreOf 2 X' := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxN := hHN (hX' hx)
    constructor
    · rintro ⟨hyP, hyX⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 hxN y).1 hyP, X'.mul_mem (X'.mul_mem hx hyX)
        (X'.inv_mem hx)⟩
    · rintro ⟨hyP, hyX⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 hxN y).2 hyP, by
        have := X'.mul_mem (X'.mul_mem (X'.inv_mem hx) hyX) hx
        simpa [mul_assoc] using this⟩
  exact (le_inf hVP hVX').trans hPX'

end Generic

section F436

set_option linter.unusedSectionVars false

theorem burnsideF4j_bM_eq_bOne {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {M : Type} [Group M] (ε : Y →* M) (x : ↥(M₁ ⊓ M₂)) :
    bM β ε x = burnsideF4d_bOne β ε ⟨(x : E), x.2.1⟩ :=
  rfl

theorem burnsideF4j_bOne_eq_bTwo {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {M : Type} [Group M] (ε : Y →* M) (x : E) (h1 : x ∈ M₁) (h2 : x ∈ M₂) :
    burnsideF4d_bOne β ε ⟨x, h1⟩ = burnsideF4d_bTwo β ε ⟨x, h2⟩ := by
  have e1 : β.φ1 (⟨x, h1⟩ : ↥M₁) = β.φ2 (⟨x, h2⟩ : ↥M₂) := by
    have a1 := β.comm1 (⟨x, h1, h2⟩ : ↥(M₁ ⊓ M₂))
    have a2 := β.comm2 (⟨x, h1, h2⟩ : ↥(M₁ ⊓ M₂))
    exact a1.trans a2.symm
  show epsG β ε (f1 (c := β) ⟨x, h1⟩) = epsG β ε (f2 (c := β) ⟨x, h2⟩)
  congr 1
  exact Subtype.ext e1

theorem burnsideF4j_subImg_cenIn_le {Mb G : Type} [Group Mb] [Group G] {N : Subgroup Mb}
    (b : ↥N →* G) (X : Subgroup Mb) {r : Mb} (hr : r ∈ N) :
    subImg b (cenIn X r) ≤ Subgroup.centralizer ({b ⟨r, hr⟩} : Set G) := by
  intro y hy
  obtain ⟨x, hxN, ⟨-, hxr⟩, rfl⟩ := mem_subImg.mp hy
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hxr)

theorem burnsideF4j_F436_core {E : Type} [Group E] [Finite E] {M : Type} [Group M] [Finite M]
    {N N' : Subgroup E} (b : ↥N →* M) (b' : ↥N' →* M) (hb : Function.Injective b)
    (hb' : Function.Injective b')
    (hagree : ∀ (x : E) (h1 : x ∈ N) (h2 : x ∈ N'), b ⟨x, h1⟩ = b' ⟨x, h2⟩)
    {H : Subgroup M} (hH : IsSylowTwoOf (pCoreOf 2 (oTwoRes H)) (oTwoRes H))
    {X X' : Subgroup E} (hXN : X ≤ N) (hX'N' : X' ≤ N')
    (hXH : subImg b X ≤ H) (hX'H : subImg b' X' ≤ H)
    (hV : pCoreOf 2 (oTwoRes X) ≤ X') : pCoreOf 2 (oTwoRes X) ≤ pCoreOf 2 X' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := pCoreOf 2 (oTwoRes X)
  have hVX : V ≤ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (oTwoRes_le X)
  have hVN : V ≤ N := hVX.trans hXN
  have hVN' : V ≤ N' := hV.trans hX'N'
  have hVimg : subImg b V = subImg b' V := subImg_eq_of_agree hagree hVN hVN'
  have hpV : IsPGroup 2 (subImg b V) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).of_equiv (burnsideF4j_subImgEquiv b hb hVN)
  have h1 : subImg b V ≤ oTwoRes (subImg b X) := by
    rw [burnsideF4j_oTwoRes_subImg b hb hXN]
    exact subImg_mono b (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have h2 : subImg b V ≤ subImg b' X' := by
    rw [hVimg]; exact subImg_mono b' hV
  have h3 := burnsideF4j_le_pCoreOf_of_twoClosed hXH hX'H hH hpV h1 h2
  rw [subImg_pCoreOf hb' hX'N', hVimg] at h3
  intro v hv
  have hvN' : v ∈ N' := hVN' hv
  have := h3 (mem_subImg_of_mem b' hvN' hv)
  exact (mem_subImg_iff_of_injective hb' hvN').1 this

end F436

end CFSG.ASVolI
