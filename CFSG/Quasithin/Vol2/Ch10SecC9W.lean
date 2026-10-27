module

public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowTwoOf_of_le {S R H : Subgroup G} (hS : IsSylowTwoOf S H) (hSR : S ≤ R)
    (hRH : R ≤ H) (hR : IsPGroup 2 R) : IsSylowTwoOf R H := by
  refine ⟨hRH, hR, fun h => hS.2.2 ?_⟩
  show 2 ∣ S.relIndex H
  rw [← Subgroup.relIndex_mul_relIndex S R H hSR hRH]
  exact Dvd.dvd.mul_left h _

theorem isSylowTwoOf_of_normalizer_le {M H S : Subgroup G} (hS : IsSylowTwoOf S (M ⊓ H))
    (hN : H ⊓ Subgroup.normalizer (S : Set G) ≤ M) : IsSylowTwoOf S H := by
  have hSH : S ≤ H := hS.1.trans inf_le_right
  obtain ⟨R, hR, hSR⟩ := A4.exists_isSylowTwoOf_ge hSH hS.2.1
  rcases eq_or_lt_of_le hSR with h | h
  · rw [h]
    exact hR
  · exfalso
    obtain ⟨s, hsR, hsN, hsS⟩ := A4.exists_mem_normalizer_not_mem hR.2.1 h
    have hsM : s ∈ M := hN ⟨hR.1 hsR, hsN⟩
    have hmax := (A4.isSylowTwoOf_iff_maximal.mp hS).2.2 (R ⊓ M)
      (fun x hx => ⟨hx.2, hR.1 hx.1⟩) (hR.2.1.to_inf_left) (le_inf hSR (hS.1.trans inf_le_left))
    exact hsS (hmax ⟨hsR, hsM⟩)

omit [Finite G] in
theorem conjSub_inf_centralizer {M : Subgroup G} {m : G} (hm : m ∈ M) (u : G) :
    B6.conjSub m (M ⊓ Subgroup.centralizer ({u} : Set G)) =
      M ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G) := by
  ext x
  rw [B6.mem_conjSub, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · have := M.mul_mem (M.mul_mem hm hx1) (M.inv_mem hm)
      have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
      rwa [e] at this
    · calc x * (m * u * m⁻¹) = m * ((m⁻¹ * x * m) * u) * m⁻¹ := by group
        _ = m * (u * (m⁻¹ * x * m)) * m⁻¹ := by rw [hx2]
        _ = m * u * m⁻¹ * x := by group
  · rintro ⟨hx1, hx2⟩
    refine ⟨M.mul_mem (M.mul_mem (M.inv_mem hm) hx1) hm, ?_⟩
    calc m⁻¹ * x * m * u = m⁻¹ * (x * (m * u * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * u * m⁻¹) * x) * m := by rw [hx2]
      _ = u * (m⁻¹ * x * m) := by group

theorem exists_isSylowTwoOf_centralizer {M T : Subgroup G} (hT : IsSylowTwoOf T M) (u : G) :
    ∃ m ∈ M, IsSylowTwoOf (T ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G))
        (M ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G)) ∧
      ∀ x ∈ T ⊓ Subgroup.centralizer ({u} : Set G),
        m * x * m⁻¹ ∈ T ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G) := by
  have hP : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer ({u} : Set G)) := hT.2.1.to_inf_left
  obtain ⟨S₁, hS₁, hPS₁⟩ := A4.exists_isSylowTwoOf_ge
    (inf_le_inf_right (Subgroup.centralizer ({u} : Set G)) hT.1) hP
  obtain ⟨S₂, hS₂, hS₁S₂⟩ := A4.exists_isSylowTwoOf_ge (hS₁.1.trans inf_le_left) hS₁.2.1
  obtain ⟨h, hh, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hT hS₂
  set m := h⁻¹ with hmdef
  have hm : m ∈ M := M.inv_mem hh
  have hS₁T : ∀ x ∈ S₁, m * x * m⁻¹ ∈ T := fun x hx => by
    have := (hconj x).mp (hS₁S₂ hx)
    rwa [hmdef, inv_inv]
  have hS₁c : ∀ x ∈ S₁, m * x * m⁻¹ ∈ Subgroup.centralizer ({m * u * m⁻¹} : Set G) :=
    fun x hx => by
      have hxc : x * u = u * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hS₁.1 hx).2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc m * x * m⁻¹ * (m * u * m⁻¹) = m * (x * u) * m⁻¹ := by group
        _ = m * (u * x) * m⁻¹ := by rw [hxc]
        _ = m * u * m⁻¹ * (m * x * m⁻¹) := by group
  have hle : B6.conjSub m S₁ ≤ T ⊓ Subgroup.centralizer ({m * u * m⁻¹} : Set G) := by
    intro y hy
    rw [B6.mem_conjSub] at hy
    have e : m * (m⁻¹ * y * m) * m⁻¹ = y := by group
    rw [← e]
    exact ⟨hS₁T _ hy, hS₁c _ hy⟩
  have hSyl := B6.isSylowTwoOf_conjSub hS₁ m
  rw [conjSub_inf_centralizer hm] at hSyl
  refine ⟨m, hm, isSylowTwoOf_of_le hSyl hle (inf_le_inf_right _ hT.1) hT.2.1.to_inf_left,
    fun x hx => ⟨hS₁T x (hPS₁ hx), hS₁c x (hPS₁ hx)⟩⟩

omit [Finite G] in
theorem le_thompsonJ_of_isMaxElemAbelian {T A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    A ≤ thompsonJ T :=
  le_iSup₂ (f := fun (B : Subgroup G) (_ : IsMaxElemAbelian T B) => B) A hA

theorem conjSub_thompsonJ_eq {T : Subgroup G} {g : G} (h : B6.conjSub g (thompsonJ T) ≤ T) :
    B6.conjSub g (thompsonJ T) = thompsonJ T := by
  have hle : B6.conjSub g (thompsonJ T) ≤ thompsonJ T := by
    show (thompsonJ T).map (MulAut.conj g).toMonoidHom ≤ thompsonJ T
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hAJ : A ≤ thompsonJ T := le_thompsonJ_of_isMaxElemAbelian hA
    have hAg : B6.conjSub g A ≤ T := ((B6.conjSub g).monotone hAJ).trans h
    refine le_thompsonJ_of_isMaxElemAbelian (A := B6.conjSub g A)
      ⟨hAg, B6.isElemAbelian_conjSub hA.2.1 g, fun B hBT hB => ?_⟩
    rw [B6.card_conjSub]
    exact hA.2.2 B hBT hB
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [B6.card_conjSub])

theorem baum_le_centralizer_of_mem {T V : Subgroup G} (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    {x : G} (hx : x ∈ V) (hxJ : x ∈ Subgroup.centralizer (thompsonJ T : Set G)) :
    baum T ≤ Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  have hAJ := le_thompsonJ_of_isMaxElemAbelian hA
  have hxA : x ∈ A := inf_centralizer_le_of_isMaxElemAbelian hV hVT hA
    ⟨hx, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAJ) hxJ⟩
  have hxZ : x ∈ omegaOneCenterOf (thompsonJ T) :=
    Subgroup.subset_closure ⟨⟨hAJ hxA, hxJ⟩, hV.2 x hx⟩
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hs.2 x hxZ).symm

end CFSG.Quasithin.Vol2.Ch10.SecC
