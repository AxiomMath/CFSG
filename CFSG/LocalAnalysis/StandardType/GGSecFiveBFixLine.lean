module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGRowKFrame
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

structure GGFixLineComp (Bs : Subgroup G) (u : G) (P : Subgroup G) : Prop where
  mem : u ∈ Bs
  isComponentOf : IsComponentOf P (Subgroup.centralizer ({u} : Set G))
  fix_iff : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer P Bs, φ b = b) ↔ (b : G) ∈ Subgroup.zpowers u

theorem GGFixLineComp.of_inf_centralizer [Finite G] {Bs P : Subgroup G} {u : G} (hu : u ∈ Bs)
    (hP : IsComponentOf P (Subgroup.centralizer ({u} : Set G)))
    (hzp : Bs ⊓ Subgroup.centralizer (P : Set G) = Subgroup.zpowers u)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer P Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers u) :
    GGFixLineComp Bs u P := by
  refine ⟨hu, hP, fun b => ⟨hfix b, fun hb φ hφ => ?_⟩⟩
  have hb' : (b : G) ∈ Bs ⊓ Subgroup.centralizer (P : Set G) := by
    rw [hzp]
    exact hb
  have hPb : P ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact (Subgroup.mem_centralizer_iff.mp hb'.2 g hg).symm
  exact ggRC_automizer_fixes_y (K := P) b.2 hPb φ hφ

theorem GGConfig.fixLineComp_L_of_fix [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hc : GGConfig p B Bs x L D J)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x) :
    GGFixLineComp Bs x L :=
  GGFixLineComp.of_inf_centralizer hc.tableB_facts.2.2.1 hc.1.2.2.2.2.2.2.1.2.2.2.1
    hc.bstar_inf_centralizer_L hfix

theorem GGConfig.fixLineComp_nbr_of_fix [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hc : GGConfig p B Bs x L D J) (hB : B = Bs)
    (hn : GGNbr p B x D J y K)
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (K : Set G)) :
    GGFixLineComp Bs y K := by
  subst hB
  have hzp : B ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    inf_centralizer_eq_zpowers_of_sHat hn.1
  refine GGFixLineComp.of_inf_centralizer hn.1.2.1 (isComponentOf_of_isNeighborOf
    hc.1.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hc.2.2 hn)).1 hzp fun b hb => ?_
  have hbK : (b : G) ∈ B ⊓ Subgroup.centralizer (K : Set G) := ⟨b.2, hfix b hb⟩
  rwa [hzp] at hbK

theorem GGSecFiveRestHyp.fixLineComp_L [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hTBF : GGTBFixInput) (hR : GGSecFiveRestHyp p B Bs x L D J)
    (hW : GGSecFiveWeylCase' p B Bs x D J) : GGFixLineComp Bs x L := by
  have hc : GGConfig p B Bs x L D J := hR.1
  obtain ⟨y, K, hN⟩ := exists_ggNbr hc.1.2.2.2.2.2.2.2 hc.2.2
  exact hc.fixLineComp_L_of_fix fun b hb => hTBF G p B Bs x L D J hc hR.2.1 hR.2.2.1 hR.2.2.2.1
    y K hN (hW y K hN) (Or.inr hW) b hb

theorem GGSecFiveRestHyp.fixLineComp_nbr [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J) (hB : B = Bs)
    (hn : GGNbr p B x D J y K) : GGFixLineComp Bs y K := by
  have hH : GGResHyp p B Bs x L D J y K :=
    ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1, hn, hW y K hn, Or.inr hW⟩
  exact hR.1.fixLineComp_nbr_of_fix hB hn fun b hb => hFC G p B Bs x L D J y K hH b hb

theorem GGFixLineComp.card_fix {p : ℕ} {Bs P : Subgroup G} {u : G} (h : GGFixLineComp Bs u P)
    (hp : p.Prime) (hBs : IsElemAbelian p Bs) (hu : u ≠ 1) :
    Nat.card {b : ↥Bs // ∀ φ ∈ ggAutomizer P Bs, φ b = b} = p := by
  have hle : Subgroup.zpowers u ≤ Bs := Subgroup.zpowers_le.mpr h.mem
  have hcard : Nat.card {b : ↥Bs // ∀ φ ∈ ggAutomizer P Bs, φ b = b} =
      Nat.card ↥(Subgroup.zpowers u) :=
    Nat.card_congr
      { toFun := fun b => ⟨b.1, (h.fix_iff b.1).1 b.2⟩
        invFun := fun t => ⟨⟨t.1, hle t.2⟩, (h.fix_iff ⟨t.1, hle t.2⟩).2 t.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have := Fact.mk hp
  rw [hcard, Nat.card_zpowers, orderOf_eq_prime (hBs.2 u h.mem) hu]

theorem forall_map_congr_fix_iff {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (A : Subgroup (MulAut X)) (b : X) :
    (∀ w ∈ A.map (MulAut.congr e).toMonoidHom, w (e b) = e b) ↔ ∀ ψ ∈ A, ψ b = b := by
  constructor
  · intro h ψ hψ
    have h1 := h _ ⟨ψ, hψ, rfl⟩
    change e (ψ (e.symm (e b))) = e b at h1
    rw [MulEquiv.symm_apply_apply] at h1
    exact e.injective h1
  · rintro h w hw
    obtain ⟨ψ, hψ, rfl⟩ := hw
    change e (ψ (e.symm (e b))) = e b
    rw [MulEquiv.symm_apply_apply, h ψ hψ]

theorem GGFixLineComp.forall_map_congr_fix_iff {Bs P : Subgroup G} {u : G}
    (h : GGFixLineComp Bs u P) {V : Type*} [Group V] (eta : ↥Bs ≃* V) (f : V) :
    (∀ w ∈ (ggAutomizer P Bs).map (MulAut.congr eta).toMonoidHom, w f = f) ↔
      ((eta.symm f : ↥Bs) : G) ∈ Subgroup.zpowers u := by
  have h1 := CFSG.StandardType.forall_map_congr_fix_iff eta (ggAutomizer P Bs) (eta.symm f)
  simp only [MulEquiv.apply_symm_apply] at h1
  rw [h1]
  exact h.fix_iff (eta.symm f)

theorem ggAutomizer_map_conj {Bs : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (X : Subgroup G) :
    ggAutomizer (X.map (MulAut.conj g).toMonoidHom) Bs =
      (ggAutomizer X Bs).map (MulAut.conj (ggConjAut Bs hg)).toMonoidHom := by
  rw [ggAutomizer_eq, ggAutomizer_eq]
  apply le_antisymm
  · rintro φ ⟨h', hh'X, hh'N, hφ'⟩
    rcases hh'X with ⟨h, hhX, rfl⟩
    have hhN : h ∈ Subgroup.normalizer (Bs : Set G) := by
      have hmem := Subgroup.mul_mem (Subgroup.normalizer (Bs : Set G))
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hh'N) hg
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmem
      rwa [show g⁻¹ * (g * h * g⁻¹) * g = h by group] at hmem
    refine Subgroup.mem_map.mpr ⟨ggConjAut Bs hhN, ggConjAut_mem_ggInduced hhX hhN, ?_⟩
    ext b
    rw [hφ' b]
    have hinv : ∀ c : ↥Bs, (((ggConjAut Bs hg)⁻¹ c : ↥Bs) : G) = g⁻¹ * c * g :=
      fun c => inv_apply_of_forall (ggConjAut_apply Bs hg) c
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      ggConjAut_apply, hinv]
    group
  · rintro φ ⟨ψ, hψ, rfl⟩
    rcases hψ with ⟨h, hhX, hhN, hψ'⟩
    have hh'N : g * h * g⁻¹ ∈ Subgroup.normalizer (Bs : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hhN) (Subgroup.inv_mem _ hg)
    have hh'X : g * h * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨h, hhX, rfl⟩
    have hφeq : MulAut.conj (ggConjAut Bs hg) ψ = ggConjAut Bs hh'N := by
      ext b
      have hinv : ∀ c : ↥Bs, (((ggConjAut Bs hg)⁻¹ c : ↥Bs) : G) = g⁻¹ * c * g :=
        fun c => inv_apply_of_forall (ggConjAut_apply Bs hg) c
      simp only [MulAut.conj_apply, MulAut.mul_apply, ggConjAut_apply, hψ', hinv]
      group
    change MulAut.conj (ggConjAut Bs hg) ψ ∈
      ggInducedSubgroup (X.map (MulAut.conj g).toMonoidHom) Bs
    rw [hφeq]
    exact ggConjAut_mem_ggInduced hh'X hh'N

private theorem congr_conj_apply {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (d φ : MulAut X) :
    MulAut.congr e (MulAut.conj d φ) = MulAut.conj (MulAut.congr e d) (MulAut.congr e φ) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem map_congr_ggAutomizer_map_conj {V : Type*} [Group V] {Bs : Subgroup G}
    (eta : ↥Bs ≃* V) {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (X : Subgroup G) :
    (ggAutomizer (X.map (MulAut.conj g).toMonoidHom) Bs).map (MulAut.congr eta).toMonoidHom =
      ((ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom).map
        (MulAut.conj (MulAut.congr eta (ggConjAut Bs hg))).toMonoidHom := by
  rw [ggAutomizer_map_conj hg X]
  have hcomp : ((MulAut.congr eta).toMonoidHom.comp (MulAut.conj (ggConjAut Bs hg)).toMonoidHom) =
      ((MulAut.conj (MulAut.congr eta (ggConjAut Bs hg))).toMonoidHom.comp
        (MulAut.congr eta).toMonoidHom) :=
    MonoidHom.ext fun φ => congr_conj_apply eta _ φ
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem isComponentOf_centralizer_map_conj {u : G} {P : Subgroup G}
    (h : IsComponentOf P (Subgroup.centralizer ({u} : Set G))) (g : G) :
    IsComponentOf (P.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({g * u * g⁻¹} : Set G)) := by
  have hcent : (Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * u * g⁻¹} : Set G) := by
    simpa only [MulAut.conj_apply] using CFSG.centralizer_singleton_map (MulAut.conj g) u
  rw [← hcent]
  exact (isComponentOf_iff_open).mpr
    (CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (MulAut.conj g)
      ((isComponentOf_iff_open).mp h))

theorem GGFixLineComp.map_conj {Bs X : Subgroup G} {u g : G} (h : GGFixLineComp Bs u X)
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) :
    GGFixLineComp Bs (g * u * g⁻¹) (X.map (MulAut.conj g).toMonoidHom) := by
  have hmem : g * u * g⁻¹ ∈ Bs :=
    (Subgroup.mem_normalizer_iff.mp hg u).mp h.mem
  refine ⟨hmem, isComponentOf_centralizer_map_conj h.isComponentOf g, fun b => ?_⟩
  rw [ggAutomizer_map_conj hg X]
  rw [forall_map_conj_fix_iff (ggAutomizer X Bs) (ggConjAut Bs hg) b]
  rw [h.fix_iff ((ggConjAut Bs hg)⁻¹ b)]
  have hdelta : (((ggConjAut Bs hg)⁻¹ b : ↥Bs) : G) = g⁻¹ * (b : G) * g :=
    inv_apply_of_forall (ggConjAut_apply Bs hg) b
  rw [hdelta]
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [conj_zpow, hk]
    group
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [conj_zpow] at hk
    rw [← hk]
    group

end CFSG.StandardType

end
