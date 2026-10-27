module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aULift
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private def uc22s2112r34_on_stabilizer (L : Subgroup G) (K : Subgroup (BarInf L)) :
    Subgroup ↥(normalizer (L : Set G)) where
  carrier := {g | K.map (inducedBarInfAutHom L g) = K}
  one_mem' := by
    change K.map (inducedBarInfAutHom L 1) = K
    have h1 : inducedBarInfAutHom L (1 : ↥(normalizer (L : Set G))) = 1 := map_one _
    rw [h1]
    have h2 : ((1 : MulAut (BarInf L)) : BarInf L →* BarInf L) = MonoidHom.id (BarInf L) := by
      ext x
      rfl
    rw [h2, Subgroup.map_id]
  mul_mem' := by
    intro g h hg hh
    change K.map (inducedBarInfAutHom L (g * h)) = K
    rw [map_mul]
    have hcomp : ((inducedBarInfAutHom L g * inducedBarInfAutHom L h) :
        BarInf L →* BarInf L) =
        ((inducedBarInfAutHom L g) : BarInf L →* BarInf L).comp
          ((inducedBarInfAutHom L h) : BarInf L →* BarInf L) := rfl
    rw [hcomp, ← Subgroup.map_map, hh, hg]
  inv_mem' := by
    intro g hg
    change K.map (inducedBarInfAutHom L g⁻¹) = K
    have hcomp : (inducedBarInfAutHom L g⁻¹).toMonoidHom.comp
        ((inducedBarInfAutHom L g) : BarInf L →* BarInf L) = MonoidHom.id (BarInf L) := by
      ext x
      simp
    have h := congrArg (fun H : Subgroup (BarInf L) =>
      H.map (inducedBarInfAutHom L g⁻¹).toMonoidHom) hg
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
    exact h.symm

omit [Finite G] in
private theorem uc22s2112r34_on_mem_stabilizer (L : Subgroup G) (K : Subgroup (BarInf L))
    (g : ↥(normalizer (L : Set G))) :
    g ∈ uc22s2112r34_on_stabilizer L K ↔
      K.map (inducedBarInfAutHom L g) = K := Iff.rfl

private noncomputable def uc22s2112r34_on_rho (L : Subgroup G) (K : Subgroup (BarInf L)) :
    ↥(uc22s2112r34_on_stabilizer L K) →* MulAut ↥K where
  toFun g :=
    (MulEquiv.subgroupMap (inducedBarInfAutHom L g.1) K).trans
      (MulEquiv.subgroupCongr ((uc22s2112r34_on_mem_stabilizer L K g.1).mp g.2))
  map_one' := by
    apply MulEquiv.ext
    intro k
    refine Subtype.ext ?_
    change inducedBarInfAutHom L (1 : ↥(normalizer (L : Set G))) (k : BarInf L) = (k : BarInf L)
    rw [map_one]
    rfl
  map_mul' := by
    intro g h
    apply MulEquiv.ext
    intro k
    refine Subtype.ext ?_
    change inducedBarInfAutHom L ((g : ↥(normalizer (L : Set G))) *
        (h : ↥(normalizer (L : Set G)))) (k : BarInf L) =
      inducedBarInfAutHom L (g : ↥(normalizer (L : Set G)))
        (inducedBarInfAutHom L (h : ↥(normalizer (L : Set G))) (k : BarInf L))
    rw [map_mul]
    rfl

omit [Finite G] in
private theorem uc22s2112r34_on_rho_apply (L : Subgroup G) (K : Subgroup (BarInf L))
    (g : ↥(uc22s2112r34_on_stabilizer L K)) (k : ↥K) :
    ((uc22s2112r34_on_rho L K g) k : BarInf L) = inducedBarInfAutHom L g.1 k := by
  change ((MulEquiv.subgroupCongr ((uc22s2112r34_on_mem_stabilizer L K g.1).mp g.2))
    ((MulEquiv.subgroupMap (inducedBarInfAutHom L g.1) K) k) : BarInf L) =
      inducedBarInfAutHom L g.1 k
  rw [MulEquiv.subgroupCongr_apply]
  exact MulEquiv.coe_subgroupMap_apply (inducedBarInfAutHom L g.1) K k

omit [Finite G] in
private theorem uc22s2112r34_on_rho_inv_apply (L : Subgroup G) (K : Subgroup (BarInf L))
    (g : ↥(uc22s2112r34_on_stabilizer L K)) (k : ↥K) :
    (((uc22s2112r34_on_rho L K g)⁻¹) k : BarInf L) =
      (inducedBarInfAutHom L g.1)⁻¹ k := by
  rw [← map_inv, uc22s2112r34_on_rho_apply]
  exact congrArg (fun e : MulAut (BarInf L) => e k)
    (map_inv (inducedBarInfAutHom L) g.1)

omit [Finite G] in
private theorem uc22s2112r34_on_rho_eq_one_iff (L : Subgroup G) (K : Subgroup (BarInf L))
    (g : ↥(uc22s2112r34_on_stabilizer L K)) :
    uc22s2112r34_on_rho L K g = 1 ↔
      ∀ k ∈ K, inducedBarInfAutHom L g.1 k = k := by
  constructor
  · intro h k hk
    have h1 := congrArg (fun e : MulAut ↥K => ((e ⟨k, hk⟩ : ↥K) : BarInf L)) h
    simpa [uc22s2112r34_on_rho_apply] using h1
  · intro h
    ext k
    rw [uc22s2112r34_on_rho_apply]
    simpa using h k k.2

theorem uc22s2112r34_false_of_inverts_on {D : Data G} (c : Ctx21 D (Choice214U D))
    {L : Subgroup G} (hBN : c.B0 ≤ normalizer (L : Set G)) (hB0 : c.B0 ≠ ⊥)
    {K : Subgroup (BarInf L)}
    (hKB : ∀ b (hb : b ∈ c.B0), K.map (inducedBarInfAutHom L ⟨b, hBN hb⟩).toMonoidHom = K)
    (hfaithK : ∀ b (hb : b ∈ c.B0), (∀ k ∈ K, inducedBarInfAutHom L ⟨b, hBN hb⟩ k = k) → b = 1)
    {t : G} (htT : t ∈ D.T) (htN : t ∈ normalizer (L : Set G))
    (htK : K.map (inducedBarInfAutHom L ⟨t, htN⟩).toMonoidHom = K)
    (hinv : ∀ b (hb : b ∈ c.B0), ∀ k ∈ K, (inducedBarInfAutHom L ⟨t, htN⟩ *
      inducedBarInfAutHom L ⟨b, hBN hb⟩ * (inducedBarInfAutHom L ⟨t, htN⟩)⁻¹) k =
        (inducedBarInfAutHom L ⟨b, hBN hb⟩)⁻¹ k) : False := by
  set N : Subgroup G := normalizer (L : Set G) with hNdef
  set θ : ↥N →* MulAut (BarInf L) := inducedBarInfAutHom L with hθdef
  set Γ : Subgroup ↥N := uc22s2112r34_on_stabilizer L K with hΓdef
  set B' : Subgroup ↥N := c.B0.subgroupOf N with hB'def
  set S' : Subgroup ↥N := (D.T ⊓ N).subgroupOf N with hS'def
  set B : Subgroup ↥Γ := B'.subgroupOf Γ with hBdef
  set S : Subgroup ↥Γ := (S' ⊓ Γ).subgroupOf Γ with hSdef
  set s : ↥Γ := ⟨⟨t, htN⟩, htK⟩ with hsdef
  have hΓmem : ∀ g : ↥N, g ∈ Γ ↔ K.map (θ g).toMonoidHom = K := by
    intro g
    rw [hΓdef]
    rfl
  have hB'Γ : B' ≤ Γ := by
    intro b hb
    rw [hΓmem]
    have hbG : (b : G) ∈ c.B0 := by
      rw [hB'def] at hb
      exact Subgroup.mem_subgroupOf.mp hb
    simpa [hθdef] using hKB (b : G) hbG
  obtain ⟨-, -, -, -, -, -, -, -, -, hperm, -, -⟩ := c.hB0
  have hcomm := CFSG.Quasithin.H23P4.mul_comm_inf_of_le (S := D.T) (Y := c.B0) (N := N)
    hperm.symm hBN
  have hBS' : (B' : Set ↥N) * (S' : Set ↥N) = (S' : Set ↥N) * (B' : Set ↥N) :=
    CFSG.Quasithin.H23P4.mul_comm_subgroupOf (A := c.B0) (B := D.T ⊓ N) (N := N)
      hBN inf_le_right hcomm.symm
  have hBSinf : ((S' ⊓ Γ : Subgroup ↥N) : Set ↥N) * (B' : Set ↥N) =
      (B' : Set ↥N) * ((S' ⊓ Γ : Subgroup ↥N) : Set ↥N) :=
    CFSG.Quasithin.H23P4.mul_comm_inf_of_le (S := S') (Y := B') (N := Γ) hBS'.symm hB'Γ
  have hBS : (B : Set ↥Γ) * (S : Set ↥Γ) = (S : Set ↥Γ) * (B : Set ↥Γ) :=
    CFSG.Quasithin.H23P4.mul_comm_subgroupOf (A := B') (B := S' ⊓ Γ) (N := Γ)
      hB'Γ inf_le_right hBSinf.symm
  have hS'2 : IsPGroup 2 S' :=
    (D.sylowM.isPGroup.to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hS : IsPGroup 2 S :=
    (hS'2.to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : S' ⊓ Γ ≤ Γ)).symm
  have hBo' : Odd (Nat.card B') := by
    rw [hB'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv]
    exact ch214_odd_card c.hpi
  have hBo : Odd (Nat.card B) := by
    rw [hBdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'Γ).toEquiv]
    exact hBo'
  have hfaithB : ∀ b ∈ B, uc22s2112r34_on_rho L K b = 1 → b = 1 := by
    intro b hb h1
    have hb1 : b ∈ B'.subgroupOf Γ := by
      rwa [hBdef] at hb
    have hb' : (b : ↥N) ∈ B' := Subgroup.mem_subgroupOf.mp hb1
    have hbG : (b : G) ∈ c.B0 := by
      rw [hB'def] at hb'
      exact Subgroup.mem_subgroupOf.mp hb'
    have h2 : ∀ k ∈ K, inducedBarInfAutHom L b.1 k = k :=
      (uc22s2112r34_on_rho_eq_one_iff L K b).mp h1
    exact Subtype.ext (Subtype.ext (hfaithK (b : G) hbG h2))
  have hs : s ∈ S := by
    rw [hSdef, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hS'def]
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨htT, htN⟩)
    · exact (hΓmem (s : ↥N)).mpr (by simpa [hθdef] using htK)
  have hinvΓ : ∀ b ∈ B, uc22s2112r34_on_rho L K s * uc22s2112r34_on_rho L K b *
      (uc22s2112r34_on_rho L K s)⁻¹ = (uc22s2112r34_on_rho L K b)⁻¹ := by
    intro b hb
    ext k
    have hb1 : b ∈ B'.subgroupOf Γ := by
      rwa [hBdef] at hb
    have hb' : (b : ↥N) ∈ B' := Subgroup.mem_subgroupOf.mp hb1
    have hbG : (b : G) ∈ c.B0 := by
      rw [hB'def] at hb'
      exact Subgroup.mem_subgroupOf.mp hb'
    have hLHS : ((uc22s2112r34_on_rho L K s * uc22s2112r34_on_rho L K b *
        (uc22s2112r34_on_rho L K s)⁻¹) k : BarInf L) =
        (inducedBarInfAutHom L ⟨t, htN⟩ * inducedBarInfAutHom L ⟨b, hBN hbG⟩ *
          (inducedBarInfAutHom L ⟨t, htN⟩)⁻¹) (k : BarInf L) := by
      simp only [uc22s2112r34_on_rho_apply, uc22s2112r34_on_rho_inv_apply,
        MulAut.mul_apply, hsdef]
      rfl
    rw [hLHS, uc22s2112r34_on_rho_inv_apply]
    simpa [hθdef] using hinv (b : G) hbG (k : BarInf L) k.2
  obtain ⟨t', ht'S, ht'inv⟩ :=
    uc22s2112u_lift_inv (uc22s2112r34_on_rho L K) hS hBo hBS hfaithB hs hinvΓ
  have ht'T : ((t' : ↥Γ) : G) ∈ D.T := by
    have h1 : (t' : ↥N) ∈ S' := by
      have h := ht'S
      rw [hSdef] at h
      exact (Subgroup.mem_subgroupOf.mp h).1
    rw [hS'def] at h1
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h1)).1
  have hinvG : ∀ b ∈ c.B0, ((t' : ↥Γ) : G) * b * (((t' : ↥Γ) : G))⁻¹ = b⁻¹ := by
    intro b hb
    let bΓ : ↥Γ := ⟨⟨b, hBN hb⟩, hKB b hb⟩
    have hbB : bΓ ∈ B := by
      rw [hBdef, Subgroup.mem_subgroupOf, hB'def, Subgroup.mem_subgroupOf]
      simpa [bΓ] using hb
    have h := congrArg (fun x : ↥Γ => ((x : ↥N) : G)) (ht'inv bΓ hbB)
    simpa [bΓ] using h
  have ht'Norm : ((t' : ↥Γ) : G) ∈ normalizer (c.B0 : Set G) :=
    uc22s2112u_mem_normalizer_of_inv hinvG
  obtain ⟨hi, -⟩ := c.hch
  exact hi hB0 ((t' : ↥Γ) : G) ht'T ht'Norm hinvG

end CFSG.LocalAnalysis.UniquenessCase.UC22
