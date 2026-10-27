module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3PU3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace ProdSetup

variable {F : FanTree Γ G} {α β : V} {x : G} {H : Subgroup G} (S : ProdSetup F α β x H)

include S

theorem comm_inf (L : LocalFacts F) (hnorm : ∀ h ∈ H, h * x * h⁻¹ ∈ Subgroup.zpowers x) {l : G}
    (hl : l ∈ nbrStab Γ G α ⊓ nbrStab Γ G β) : x * l * x⁻¹ = l := by
  have hc1 : l * x * l⁻¹ * x⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.zpowers x).mul_mem (hnorm l (S.nbrStab_le hl.2))
      ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x))
  have hxl : x * l⁻¹ * x⁻¹ ∈ nbrStab Γ G α ⊓ nbrStab Γ G β :=
    S.conj_mem_inf L S.x_mem ((nbrStab Γ G α ⊓ nbrStab Γ G β).inv_mem hl)
  have hc2 : l * x * l⁻¹ * x⁻¹ ∈ nbrStab Γ G β := by
    have := (nbrStab Γ G β).mul_mem hl.2 hxl.2
    have e : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
    rwa [e]
  have h1 : l * x * l⁻¹ * x⁻¹ = 1 := S.toXSetup.eq_one_of_mem_zpowers L hc1 hc2
  have h2 : l * x * l⁻¹ = x := mul_inv_eq_one.1 h1
  have h3 : l * x = x * l := mul_inv_eq_iff_eq_mul.1 h2
  calc x * l * x⁻¹ = l * x * x⁻¹ := by rw [h3]
    _ = l := by simp

theorem comm_nbrStab (L : LocalFacts F) (hnorm : ∀ h ∈ H, h * x * h⁻¹ ∈ Subgroup.zpowers x)
    {s : G} (hs : s ∈ nbrStab Γ G α) : x * s * x⁻¹ = s := by
  have hL := S.inf_eq_ballStab_two L
  have hu : x * s * x⁻¹ * s⁻¹ ∈ ballStab Γ G 2 α :=
    S.toXSetup.comm_mod_of_inf_eq L hL s hs
  have huK : x * s * x⁻¹ * s⁻¹ ∈ nbrStab Γ G α :=
    (nbrStab Γ G α).mul_mem (F.conj_mem_nbrStab_of_stab S.mem hs) ((nbrStab Γ G α).inv_mem hs)
  have hxu : x * (x * s * x⁻¹ * s⁻¹) * x⁻¹ = x * s * x⁻¹ * s⁻¹ :=
    S.comm_inf L hnorm (hL ▸ hu)
  obtain ⟨m, hm⟩ := (F.nbrStab_isPGroup α) ⟨_, huK⟩
  have h1 := comm_eq_one_of_central (F.odd_valence α) S.pow_valence_eq_one hxu
    (congrArg Subtype.val hm)
  have : x * s * x⁻¹ = s := by
    have := mul_inv_eq_one.1 h1
    exact this
  exact this

theorem false_of_prod (L : LocalFacts F) (h29 : Sigma3Aut) : False := by
  have hnorm : ∀ h ∈ H, h * x * h⁻¹ ∈ Subgroup.zpowers x := by
    by_cases hp3 : pval Γ α = 3
    · exact S.normal_of_valence_three L h29 hp3
    · exact S.normal_of_valence_ne_three L hp3
  exact F.false_of_centralizes L S.mem S.ord fun k hk => S.comm_nbrStab L hnorm hk

end ProdSetup

theorem fan_3_2 {F : FanTree Γ G} (L : LocalFacts F) (h29 : Sigma3Aut) : Fan32 F := by
  intro α β hαβ x hx hord
  refine ⟨?_, fun hP => (F.not_pclosed α hP).elim⟩
  rintro ⟨H, hH⟩
  exact (ProdSetup.false_of_prod ⟨⟨hαβ, hx, hord⟩, hH⟩ L h29).elim

end CFSG.Quasithin.Fan86
