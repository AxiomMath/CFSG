module

public import CFSG.Quasithin.EmptyFaithful.S153WStruct
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Cent

public section

namespace CFSG.QuasithinUnique.AppCS2W

open CFSG.QuasithinUnique.AppCS2 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

namespace WDbl

variable {t : G} (D : WDbl H S L t)
include D

theorem blockD_comm_L₂ {c a : G} (hc : c ∈ blockD S L) (ha : a ∈ conjR L t) : a * c = c * a :=
  Subgroup.mem_centralizer_iff.1 hc.2 a (D.L₂_le_K ha)

theorem H_le_normalizer_blockD : H ≤ normalizer (blockD S L : Set G) := by
  rw [D.hcs.eq_join]
  refine sup_le (fun k hk => ?_) S_le_normalizer_blockD
  exact Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun c hc => (Subgroup.mem_centralizer_iff.1 hc.2 k hk).symm)

theorem blockD_le_pCoreOf : blockD S L ≤ pCoreOf 2 H :=
  C1.le_pCoreOf_of_normalized (inf_le_left.trans D.hcs.sylow.le)
    (fun _ hg => D.H_le_normalizer_blockD hg) (D.hcs.sylow.isPGroup.to_le inf_le_left)

theorem U0_comm_of {g : G} (h1 : ∀ a ∈ blockU L, a * g = g * a)
    (h2 : ∀ b ∈ blockU2 L t, b * g = g * b) : ∀ u ∈ U0 L t, u * g = g * u := by
  intro u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := D.exists_mul_of_mem_U0 hu
  calc a * b * g = a * (b * g) := by group
    _ = a * (g * b) := by rw [h2 b hb]
    _ = (a * g) * b := by group
    _ = (g * a) * b := by rw [h1 a ha]
    _ = g * (a * b) := by group

end WDbl

namespace WTwo

variable {t x : G} (X : WTwo H S L t x)
include X

theorem P_decomp {q : G} (hq : q ∈ pCoreOf 2 H) :
    ∃ u ∈ U0 L t, ∃ c ∈ blockD S L, q = u * c := by
  have hD := X.C.D
  have hqS : q ∈ S ⊓ centralizer ((U0 L t : Subgroup G) : Set G) := by
    rw [hD.campbell_pkg.2.2.2]; exact hq
  have hqU : ∀ u ∈ U0 L t, u * q = q * u := fun u hu => Subgroup.mem_centralizer_iff.1 hqS.2 u hu
  have hbb : ∀ ℓ ∈ L, q * ℓ * q⁻¹ * ℓ⁻¹ ∈ blockU L := hD.bb1 q hq
  have hqC : ∀ u ∈ blockU L, q * u = u * q := fun u hu =>
    (hqU u (Subgroup.mem_sup_left hu)).symm
  obtain ⟨u₁, hu₁, hcent₁⟩ := exists_split_abs hD.hL hD.h5 X.C.P hbb hqC
  have hq₁ : u₁ * q ∈ pCoreOf 2 H := (pCoreOf 2 H).mul_mem (hD.U1_le_Q hu₁) hq
  have hbb₂ : ∀ ℓ ∈ conjR L t, (u₁ * q) * ℓ * (u₁ * q)⁻¹ * ℓ⁻¹ ∈ blockU (conjR L t) :=
    hD.swap.bb1 (u₁ * q) hq₁
  have hqC₂ : ∀ u ∈ blockU (conjR L t), (u₁ * q) * u = u * (u₁ * q) := by
    intro u hu
    rw [blockU_L₂] at hu
    have e1 : u₁ * u = u * u₁ := hD.U1_comm_U2 u₁ hu₁ u hu
    have e2 : q * u = u * q := (hqU u (Subgroup.mem_sup_right hu)).symm
    calc (u₁ * q) * u = u₁ * (q * u) := by group
      _ = u₁ * (u * q) := by rw [e2]
      _ = (u₁ * u) * q := by group
      _ = (u * u₁) * q := by rw [e1]
      _ = u * (u₁ * q) := by group
  obtain ⟨u₂, hu₂, hcent₂⟩ := exists_split_abs hD.hL₂ hD.h5₂ X.C'.P hbb₂ hqC₂
  rw [blockU_L₂] at hu₂
  have hcL : ∀ γ ∈ L, γ * (u₂ * (u₁ * q)) = (u₂ * (u₁ * q)) * γ := by
    intro γ hγ
    have e1 : γ * u₂ = u₂ * γ := hD.comm_elem γ hγ u₂ (hD.blockU2_le_L₂ hu₂)
    calc γ * (u₂ * (u₁ * q)) = (γ * u₂) * (u₁ * q) := by group
      _ = (u₂ * γ) * (u₁ * q) := by rw [e1]
      _ = u₂ * (γ * (u₁ * q)) := by group
      _ = u₂ * ((u₁ * q) * γ) := by rw [hcent₁ γ hγ]
      _ = (u₂ * (u₁ * q)) * γ := by group
  have hcS : u₂ * (u₁ * q) ∈ S := by
    have hP : u₂ * (u₁ * q) ∈ pCoreOf 2 H :=
      (pCoreOf 2 H).mul_mem (hD.U2_le_Q hu₂) hq₁
    exact hD.Q_le_S hP
  have hc : u₂ * (u₁ * q) ∈ blockD S L := by
    refine ⟨hcS, ?_⟩
    rw [hD.hjoin, centralizer_sup_inf]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun γ hγ => hcL γ hγ,
      Subgroup.mem_centralizer_iff.2 fun γ hγ => ?_⟩
    have := hcent₂ γ hγ
    exact this
  refine ⟨u₁⁻¹ * u₂⁻¹, ?_, u₂ * (u₁ * q), hc, by group⟩
  exact (U0 L t).mul_mem (Subgroup.mem_sup_left ((blockU L).inv_mem hu₁))
    (Subgroup.mem_sup_right ((blockU2 L t).inv_mem hu₂))

theorem blockD_comm_V₁ {c v : G} (hc : c ∈ blockD S L) (hv : v ∈ conjR (blockU L) x) :
    c * v = v * c := by
  have hD := X.C.D
  have hcS₁ : c ∈ s2SI S L := blockD_le_s2SI hc
  have hvB : v ∈ baum S := X.C.V_le_baum X.hx hv
  have h1 : c * v * c⁻¹ ∈ conjR (blockU L) x :=
    (Subgroup.mem_normalizer_iff.1 (X.s2SI_le_N_V₁ hcS₁) v).1 hv
  have h2 : c * v * c⁻¹ * v⁻¹ ∈ conjR (blockU L) x :=
    (conjR (blockU L) x).mul_mem h1 ((conjR (blockU L) x).inv_mem hv)
  have h3 : c * v * c⁻¹ * v⁻¹ ∈ blockD S L := by
    have hv' : v * c⁻¹ * v⁻¹ ∈ blockD S L :=
      (Subgroup.mem_normalizer_iff.1 (S_le_normalizer_blockD hvB.1) c⁻¹).1
        ((blockD S L).inv_mem hc)
    have e : c * v * c⁻¹ * v⁻¹ = c * (v * c⁻¹ * v⁻¹) := by group
    rw [e]
    exact (blockD S L).mul_mem hc hv'
  have h4 : c * v * c⁻¹ * v⁻¹ ∈ conjR (blockU L) x ⊓ centralizer (blockU L : Set G) :=
    Subgroup.mem_inf.2 ⟨h2, Subgroup.mem_centralizer_iff.2 fun u hu =>
      blockD_comm_L h3 (hD.blockU_le_L hu)⟩
  rw [← X.cent_U₁_V₁.2] at h4
  have hZ : c * v * c⁻¹ * v⁻¹ ∈ blockZ L :=
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 h4).1, Subgroup.mem_centralizer_iff.2 fun l hl =>
      blockD_comm_L h3 hl⟩
  rw [blockZ_eq_bot_of_alt5 hD.hL hD.h5] at hZ
  have e : c * v * c⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.1 hZ
  calc c * v = (c * v * c⁻¹ * v⁻¹) * (v * c) := by group
    _ = v * c := by rw [e, one_mul]

theorem blockD_comm_V₂ {c v : G} (hc : c ∈ blockD S L) (hv : v ∈ conjR (blockU2 L t) x) :
    c * v = v * c := by
  have hD := X.C.D
  have hcS₁ : c ∈ s2SI S L := blockD_le_s2SI hc
  have hvB : v ∈ baum S := by
    have h := X.C'.V_le_baum X.hx
    rw [blockU_L₂] at h
    exact h hv
  have h1 : c * v * c⁻¹ ∈ conjR (blockU2 L t) x :=
    (Subgroup.mem_normalizer_iff.1 (X.s2SI_le_N_V₂ hcS₁) v).1 hv
  have h2 : c * v * c⁻¹ * v⁻¹ ∈ conjR (blockU2 L t) x :=
    (conjR (blockU2 L t) x).mul_mem h1 ((conjR (blockU2 L t) x).inv_mem hv)
  have h3 : c * v * c⁻¹ * v⁻¹ ∈ blockD S L := by
    have hv' : v * c⁻¹ * v⁻¹ ∈ blockD S L :=
      (Subgroup.mem_normalizer_iff.1 (S_le_normalizer_blockD hvB.1) c⁻¹).1
        ((blockD S L).inv_mem hc)
    have e : c * v * c⁻¹ * v⁻¹ = c * (v * c⁻¹ * v⁻¹) := by group
    rw [e]
    exact (blockD S L).mul_mem hc hv'
  have h4 : c * v * c⁻¹ * v⁻¹ ∈ conjR (blockU2 L t) x ⊓ centralizer (blockU2 L t : Set G) :=
    Subgroup.mem_inf.2 ⟨h2, Subgroup.mem_centralizer_iff.2 fun u hu =>
      hD.blockD_comm_L₂ h3 (hD.blockU2_le_L₂ hu)⟩
  rw [← X.cent_U₂_V₂.2] at h4
  have hZ : c * v * c⁻¹ * v⁻¹ ∈ blockZ (conjR L t) :=
    Subgroup.mem_inf.2 ⟨by rw [blockU_L₂]; exact (Subgroup.mem_inf.1 h4).1,
      Subgroup.mem_centralizer_iff.2 fun l hl => hD.blockD_comm_L₂ h3 hl⟩
  rw [blockZ_eq_bot_of_alt5 hD.hL₂ hD.h5₂] at hZ
  have e : c * v * c⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.1 hZ
  calc c * v = (c * v * c⁻¹ * v⁻¹) * (v * c) := by group
    _ = v * c := by rw [e, one_mul]

end WTwo

end CFSG.QuasithinUnique.AppCS2W
