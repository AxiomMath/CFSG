module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBar
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

section BarDown

variable {H C : Subgroup G} {Q : Type} [Group Q] {φ : ↥H →* Q}

private theorem wc813pbd_barSub_mono {A B : Subgroup G} (hAB : A ≤ B) :
    barSub H φ A ≤ barSub H φ B := by
  change (A.subgroupOf H).map φ ≤ (B.subgroupOf H).map φ
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hAB)

private theorem wc813pbd_barPre_mono {A B : Subgroup Q} (hAB : A ≤ B) :
    barPre H φ A ≤ barPre H φ B := by
  intro g hg
  obtain ⟨hgH, hgA⟩ := mem_barPre.mp hg
  exact mem_barPre.mpr ⟨hgH, hAB hgA⟩

private theorem wc813pbd_mem_barSub_iff (hφ : IsBarMap H C φ) {L N : Subgroup G}
    (hCN : C ≤ N) (hLH : L ≤ H) (l : ↥L) :
    ((φ (Subgroup.inclusion hLH l) : Q) ∈ barSub H φ N) ↔ (l : G) ∈ N := by
  constructor
  · intro hx
    obtain ⟨k, hkN, hkφ⟩ := mem_barSub.mp hx
    have hker : φ (Subgroup.inclusion hLH l * k⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hkφ]
      group
    have hC : (l : G) * (k : G)⁻¹ ∈ C := by
      have h' := (hφ.ker_iff (Subgroup.inclusion hLH l * k⁻¹)).mp hker
      simpa using h'
    have h' : (l : G) = ((l : G) * (k : G)⁻¹) * (k : G) := by group
    rw [h']
    exact N.mul_mem (hCN hC) hkN
  · intro hlN
    exact mem_barSub.mpr ⟨Subgroup.inclusion hLH l, hlN, rfl⟩

private theorem wc813pbd_relIndex_barSub (hφ : IsBarMap H C φ) {A B : Subgroup G}
    (hCA : C ≤ A) (hBH : B ≤ H) (hAB : A ≤ B) :
    (barSub H φ A).relIndex (barSub H φ B) = A.relIndex B := by
  have hker : φ.ker = C.subgroupOf H := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφ.ker_iff k
  have hsupA : (A.subgroupOf H) ⊔ φ.ker = A.subgroupOf H := by
    rw [hker]
    exact sup_eq_left.mpr (Subgroup.subgroupOf_mono H hCA)
  have hsupB : (B.subgroupOf H) ⊔ φ.ker = B.subgroupOf H := by
    rw [hker]
    exact sup_eq_left.mpr (Subgroup.subgroupOf_mono H (hCA.trans hAB))
  change ((A.subgroupOf H).map φ).relIndex ((B.subgroupOf H).map φ) = A.relIndex B
  rw [Subgroup.relIndex_map_map, hsupA, hsupB, Subgroup.relIndex_subgroupOf hBH]

theorem barPre_barSub (hφ : IsBarMap H C φ) {X : Subgroup G} (hCX : C ≤ X) (hXH : X ≤ H) :
    barPre H φ (barSub H φ X) = X := by
  ext g
  rw [mem_barPre]
  constructor
  · rintro ⟨hg, hx⟩
    obtain ⟨y, hyX, hyφ⟩ := mem_barSub.mp hx
    have hker : ((⟨g, hg⟩ : ↥H) * y⁻¹) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyφ]
      group
    have hC : g * (y : G)⁻¹ ∈ C := by
      have h' := (hφ.ker_iff ((⟨g, hg⟩ : ↥H) * y⁻¹)).mp hker
      simpa using h'
    have hg' : g = (g * (y : G)⁻¹) * (y : G) := by group
    rw [hg']
    exact X.mul_mem (hCX hC) hyX
  · intro hgX
    exact ⟨hXH hgX, mem_barSub.mpr ⟨⟨g, hXH hgX⟩, hgX, rfl⟩⟩

theorem hasQuotShape_barSub (hφ : IsBarMap H C φ) {L N : Subgroup G} (hCN : C ≤ N)
    (hNL : N ≤ L) (hLH : L ≤ H) {P : ∀ (X : Type) [Group X], Prop}
    (h : HasQuotShape L (N : Set G) P) :
    HasQuotShape (barSub H φ L) ((barSub H φ N : Subgroup Q) : Set Q) P := by
  obtain ⟨X, hX, ψ, hψ, hker, hP⟩ := h
  let ρ : ↥L →* ↥(barSub H φ L) :=
    (φ.comp (Subgroup.inclusion hLH)).codRestrict (barSub H φ L)
      (fun l => mem_barSub.mpr ⟨Subgroup.inclusion hLH l, l.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨k, hkL, hkφ⟩ := mem_barSub.mp y.2
    refine ⟨⟨(k : G), hkL⟩, ?_⟩
    apply Subtype.ext
    change φ (Subgroup.inclusion hLH ⟨(k : G), hkL⟩) = (y : Q)
    rw [show Subgroup.inclusion hLH ⟨(k : G), hkL⟩ = k from Subtype.ext rfl]
    exact hkφ
  have hker_le : ρ.ker ≤ ψ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : φ (Subgroup.inclusion hLH l) = 1 := by
      have h2 := congrArg Subtype.val hl
      simpa [ρ] using h2
    have h2 : (l : G) ∈ N := hCN (by
      have h' := (hφ.ker_iff (Subgroup.inclusion hLH l)).mp h1
      simpa using h')
    exact (hker l).mpr h2
  let χ : ↥(barSub H φ L) →* X :=
    (MonoidHom.liftOfSurjective ρ hρ) ⟨ψ, hker_le⟩
  have hχ : ∀ l : ↥L, χ (ρ l) = ψ l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply ρ (Function.surjInv hρ)
      (Function.rightInverse_surjInv hρ) ⟨ψ, hker_le⟩ l
  refine ⟨X, hX, χ, ?_, ?_, hP⟩
  · intro x
    obtain ⟨l, hl⟩ := hψ x
    exact ⟨ρ l, by rw [hχ, hl]⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨l, rfl⟩ := hρ y
      rw [hχ] at hy
      have hlN : (l : G) ∈ N := (hker l).mp hy
      exact mem_barSub.mpr ⟨Subgroup.inclusion hLH l, hlN, rfl⟩
    · intro hy
      obtain ⟨l, rfl⟩ := hρ y
      rw [hχ]
      have hy' : (φ (Subgroup.inclusion hLH l) : Q) ∈ barSub H φ N := by
        simpa [ρ] using hy
      exact (hker l).mpr ((wc813pbd_mem_barSub_iff hφ hCN hLH l).mp hy')

theorem isComponentModN_barSub (hφ : IsBarMap H C φ) {N L : Subgroup G} (hCN : C ≤ N)
    (h : IsComponentModN N H L) :
    IsComponentModN (barSub H φ N) ⊤ (barSub H φ L) := by
  obtain ⟨hNn, hNL, hLH, hsub, hshape⟩ := h
  have hbarN : (barSub H φ N).Normal := by
    have h' := hNn.map φ hφ.surjective
    simpa [barSub] using h'
  refine ⟨?_, wc813pbd_barSub_mono hNL, le_top, ?_, ?_⟩
  · exact hbarN.subgroupOf ⊤
  · have hsub' : CFSG.Open.IsSubnormal (L.subgroupOf H) ⊤ :=
      CFSG.Open.IsSubnormal.of_mathlib ((CFSG.Open.IsSubnormal.iff_subgroupOf hLH).mp hsub)
    have hmap := CFSG.Open.IsSubnormal.map φ hsub'
    simpa [barSub, Subgroup.map_top_of_surjective φ hφ.surjective] using hmap
  · exact hasQuotShape_barSub hφ hCN hNL hLH hshape

theorem isMaxParabolicMod_barSub (hφ : IsBarMap H C φ) {N L P : Subgroup G} (hCN : C ≤ N)
    (hLH : L ≤ H) (h : IsMaxParabolicMod N L P) :
    IsMaxParabolicMod (barSub H φ N) (barSub H φ L) (barSub H φ P) := by
  obtain ⟨hNP, hPLt, hmax, S, hNS, hSL, hSpow, hSodd, hSnorm⟩ := h
  have hPL : P ≤ L := hPLt.le
  have hCP : C ≤ P := hCN.trans hNP
  have hCL : C ≤ L := hCP.trans hPL
  have hPH : P ≤ H := hPL.trans hLH
  have hCS : C ≤ S := hCN.trans hNS
  have hSH : S ≤ H := hSL.trans hLH
  refine ⟨wc813pbd_barSub_mono hNP, ?_, ?_, ?_⟩
  · have hle : barSub H φ P ≤ barSub H φ L := wc813pbd_barSub_mono hPL
    refine lt_of_le_of_ne hle ?_
    intro heq
    exact hPLt.ne (by
      rw [← barPre_barSub hφ hCP hPH, ← barPre_barSub hφ hCL hLH, heq])
  · intro Y hPY hYL
    have hP_le : P ≤ barPre H φ Y := by
      have h' := wc813pbd_barPre_mono (φ := φ) hPY.le
      rw [barPre_barSub hφ hCP hPH] at h'
      exact h'
    have hlt : P < barPre H φ Y := by
      refine lt_of_le_of_ne hP_le ?_
      intro heq
      exact hPY.ne (by
        have h' := congrArg (barSub H φ) heq
        rw [barSub_barPre hφ Y] at h'
        exact h')
    have hYleL : barPre H φ Y ≤ L := by
      have h' := wc813pbd_barPre_mono (φ := φ) hYL
      rw [barPre_barSub hφ hCL hLH] at h'
      exact h'
    have hEq : barPre H φ Y = L := hmax (barPre H φ Y) hlt hYleL
    rw [← barSub_barPre hφ Y, hEq]
  · refine ⟨barSub H φ S, wc813pbd_barSub_mono hNS, wc813pbd_barSub_mono hSL, ?_, ?_, ?_⟩
    · intro s hs
      obtain ⟨k, hkS, hks⟩ := mem_barSub.mp hs
      obtain ⟨m, hm⟩ := hSpow (k : G) hkS
      refine ⟨m, ?_⟩
      rw [← hks, ← map_pow]
      exact mem_barSub.mpr ⟨k ^ 2 ^ m, by simpa using hm, rfl⟩
    · have hidx := wc813pbd_relIndex_barSub hφ hCS hLH hSL
      rw [hidx]
      exact hSodd
    · intro y hy
      obtain ⟨hyL, hyN⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨l, hlL, rfl⟩ := mem_barSub.mp hyL
      have hnorm : barPre H φ (Subgroup.normalizer ((barSub H φ S : Subgroup Q) : Set Q)) ≤
          Subgroup.normalizer (S : Set G) := by
        have h := le_normalizer_barPre (φ := φ) hφ (Xb := barSub H φ S)
          (A := barPre H φ (Subgroup.normalizer ((barSub H φ S : Subgroup Q) : Set Q)))
          (barPre_le H φ (Subgroup.normalizer ((barSub H φ S : Subgroup Q) : Set Q)))
          (le_of_eq (barSub_barPre hφ (Subgroup.normalizer ((barSub H φ S : Subgroup Q) : Set Q))))
        rw [barPre_barSub hφ hCS hSH] at h
        exact h
      have hl_norm : (l : G) ∈ Subgroup.normalizer (S : Set G) :=
        hnorm (mem_barPre.mpr ⟨l.2, hyN⟩)
      exact mem_barSub.mpr ⟨l, hSnorm ⟨hlL, hl_norm⟩, rfl⟩

theorem actsOnDynkinMod_barSub (hφ : IsBarMap H C φ) {N L : Subgroup G} {t : G} (htH : t ∈ H)
    (hCN : C ≤ N) (hLH : L ≤ H) (h : ActsOnDynkinMod N L t) :
    ActsOnDynkinMod (barSub H φ N) (barSub H φ L) (φ ⟨t, htH⟩) := by
  obtain ⟨htn, P, hP, hconj⟩ := h
  have hPLt : P < L := hP.2.1
  have hPL : P ≤ L := hPLt.le
  have hCP : C ≤ P := hCN.trans hP.1
  have hPH : P ≤ H := hPL.trans hLH
  have hCH : C ≤ H := hCP.trans hPH
  have hCker : (C.subgroupOf H).Normal := by
    have hker : C.subgroupOf H = φ.ker := by
      ext k
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact (hφ.ker_iff k).symm
    rw [hker]
    exact MonoidHom.normal_ker φ
  have hCconj : ∀ g ∈ H, C ≤ conjSubgroup P g := by
    intro g hgH c hc
    rw [mem_conjSubgroup_iff]
    have hCnorm : H ≤ Subgroup.normalizer (C : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mp hCker
    exact hCP ((Subgroup.mem_normalizer_iff.mp (hCnorm hgH) c).mp hc)
  refine ⟨?_, barSub H φ P, isMaxParabolicMod_barSub hφ hCN hLH hP, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    have key : ∀ (u : ↥H), (u : G) ∈ Subgroup.normalizer (L : Set G) →
        ∀ y ∈ barSub H φ L, φ u * y * (φ u)⁻¹ ∈ barSub H φ L := by
      intro u hu y hy
      obtain ⟨w, hwL, rfl⟩ := mem_barSub.mp hy
      have hconjL : (u : G) * (w : G) * (u : G)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hu (w : G)).mp hwL
      exact mem_barSub.mpr ⟨u * w * u⁻¹, by simpa using hconjL, by
        rw [map_mul, map_mul, map_inv]⟩
    intro x
    constructor
    · exact key ⟨t, htH⟩ htn x
    · intro hx
      have hx' := key ⟨t, htH⟩⁻¹ ((Subgroup.normalizer (L : Set G)).inv_mem htn)
        (φ ⟨t, htH⟩ * x * (φ ⟨t, htH⟩)⁻¹) hx
      convert hx' using 1
      rw [map_inv]
      group
  · intro l' hl'
    intro heq
    obtain ⟨l, hlL, rfl⟩ := mem_barSub.mp hl'
    have hgt : t⁻¹ * (l : G) ∈ H := H.mul_mem (H.inv_mem htH) l.2
    have heq' : barSub H φ (conjSubgroup P (t⁻¹ * (l : G))) = barSub H φ P := by
      have hstep : conjSubgroup (barSub H φ P) ((φ ⟨t, htH⟩)⁻¹ * φ l) =
          barSub H φ (conjSubgroup P (t⁻¹ * (l : G))) := by
        have hphi : (φ ⟨t, htH⟩)⁻¹ * φ l = φ (⟨t, htH⟩⁻¹ * l) := by
          rw [map_mul, map_inv]
        have harg : ((⟨t, htH⟩⁻¹ * l : ↥H) : G) = t⁻¹ * (l : G) := rfl
        rw [hphi, ← barSub_conjSubgroup (φ := φ) P (⟨t, htH⟩⁻¹ * l), harg]
      rw [← hstep]
      exact heq
    have hCX : C ≤ conjSubgroup P (t⁻¹ * (l : G)) := hCconj _ hgt
    have hXH : conjSubgroup P (t⁻¹ * (l : G)) ≤ H := by
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      have hx' : x = (t⁻¹ * (l : G))⁻¹ * ((t⁻¹ * (l : G)) * x * (t⁻¹ * (l : G))⁻¹) *
          (t⁻¹ * (l : G)) := by group
      rw [hx']
      exact H.mul_mem (H.mul_mem (H.inv_mem hgt) (hPH hx)) hgt
    have hfinal : conjSubgroup P (t⁻¹ * (l : G)) = P := by
      calc conjSubgroup P (t⁻¹ * (l : G))
          = barPre H φ (barSub H φ (conjSubgroup P (t⁻¹ * (l : G)))) :=
            (barPre_barSub hφ hCX hXH).symm
        _ = barPre H φ (barSub H φ P) := by rw [heq']
        _ = P := barPre_barSub hφ hCP hPH
    exact hconj (l : G) hlL hfinal

end BarDown

end CFSG.LocalAnalysis.WeakClosure81

end
