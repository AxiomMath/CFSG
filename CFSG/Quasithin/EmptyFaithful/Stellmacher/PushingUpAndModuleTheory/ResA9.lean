module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA6
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA8

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X K V₀ : Subgroup G} {c : G}

section Bridge

variable (hX : X ≤ Subgroup.normalizer (K : Set G)) (hKd : KData K V₀ c)

include hX hKd

theorem isSec_normClosure : IsSec X ⊥ (normClosure X V₀) where
  le := bot_le
  normN := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_normClosure hy hg, fun hy => ?_⟩
    have := conj_mem_normClosure hy (X.inv_mem hg)
    simpa [mul_assoc] using this
  normL := fun g _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp [mul_eq_one_iff_eq_inv]
  comm := fun x hx y hy => by
    have := normClosure_central hX hKd hx (normClosure_le_K hX hKd hy)
    rw [this]; simp
  sq := fun x hx => by
    have := normClosure_sq hX hKd hx
    rw [pow_two, this]; exact Subgroup.one_mem _

variable (ψ : ↥X →* Perm (Fin 5)) (hψs : Function.Surjective ψ)
  (hker : ∀ x : ↥X, ψ x = 1 ↔ (x : G) ∈ K)

include hψs hker

theorem ker_le_cSec_normClosure :
    ψ.ker ≤ (cSecIn X ⊥ (normClosure X V₀)).subgroupOf X := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  rw [mem_cSecIn_iff (isSec_normClosure hX hKd).normL]
  refine ⟨x.2, fun y hy => ?_⟩
  have hxK : (x : G) ∈ K := (hker x).mp hx
  have := normClosure_central hX hKd hy hxK
  rw [← this]
  simp

@[expose] noncomputable def normModel : Model 5 :=
  secModule (isSec_normClosure hX hKd) ψ hψs (ker_le_cSec_normClosure hX hKd ψ hψs hker)

theorem normModel_nontrivial : ∃ w : (normModel hX hKd ψ hψs hker).W, w ≠ 1 := by
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V₀, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : V₀ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
    have h4 := hKd.V_card
    rw [this, Subgroup.card_bot] at h4
    omega
  refine ⟨(isSec_normClosure hX hKd).proj ⟨v, V0_le_normClosure hv⟩, fun h => hv1 ?_⟩
  have := ((isSec_normClosure hX hKd).proj_eq_one_iff _).mp h
  simpa using this

theorem odd_sign_conj {g : ↥X} (hcX : c ∈ X) :
    Perm.sign (ψ (g * ⟨c, hcX⟩ * g⁻¹)) = 1 := by
  refine sign_eq_one_of_odd (Odd.of_dvd_nat (by decide : Odd 3) ?_)
  refine orderOf_dvd_of_pow_eq_one ?_
  rw [← map_pow]
  have : (g * ⟨c, hcX⟩ * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow]
    have : (⟨c, hcX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hKd.c3)
    rw [this]; group
  rw [this, map_one]

theorem normModel_comm (hcX : c ∈ X) :
    commW (normModel hX hKd ψ hψs hker) (alternatingGroup (Fin 5)) ⊤ = ⊤ := by
  have hs := isSec_normClosure hX hKd
  set M := normModel hX hKd ψ hψs hker with hM
  rw [eq_top_iff]
  intro w _
  obtain ⟨n, rfl⟩ := hs.proj_surjective w
  set D'' : Subgroup G := ((commW M (alternatingGroup (Fin 5)) ⊤).comap hs.proj).map
    (normClosure X V₀).subtype with hD
  have hgen : normClosure X V₀ ≤ D'' := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, v, hv, rfl⟩
    obtain ⟨w0, hw0, hv'⟩ := hKd.V_comm v hv
    have hmemN : ∀ y ∈ V₀, ∀ g ∈ X, g * y * g⁻¹ ∈ normClosure X V₀ := fun y hy g hg =>
      Subgroup.subset_closure ⟨g, hg, y, hy, rfl⟩
    set u0 : ↥(normClosure X V₀) := ⟨g * w0 * g⁻¹, hmemN w0 hw0 g hg⟩ with hu0
    set gX : ↥X := ⟨g, hg⟩
    set b := ψ (gX * ⟨c, hcX⟩ * gX⁻¹) with hb
    have hbA : b ∈ alternatingGroup (Fin 5) :=
      Perm.mem_alternatingGroup.mpr (odd_sign_conj hX hKd ψ hψs hker hcX)
    refine ⟨⟨g * v * g⁻¹, hmemN v hv g hg⟩, ?_, rfl⟩
    have hact := secModule_act_proj hs ψ hψs (ker_le_cSec_normClosure hX hKd ψ hψs hker)
      (gX * ⟨c, hcX⟩ * gX⁻¹) u0
    have e1 : (⟨g * v * g⁻¹, hmemN v hv g hg⟩ : ↥(normClosure X V₀)) =
        hs.conjN (gX * ⟨c, hcX⟩ * gX⁻¹) u0 * u0⁻¹ := by
      apply Subtype.ext
      have hwa : c * w0 * c⁻¹ ∈ V₀ := hKd.V_norm w0 hw0
      have hcomm := hKd.V_cen w0 hw0 _ (hKd.V_le hwa)
      have hw2 : w0⁻¹ = w0 := inv_eq_of_mul_eq_one_right (hKd.V_sq w0 hw0)
      show g * v * g⁻¹ = (g * c * g⁻¹) * (g * w0 * g⁻¹) * (g * c * g⁻¹)⁻¹ * (g * w0 * g⁻¹)⁻¹
      calc g * v * g⁻¹ = g * (w0 * (c * w0 * c⁻¹)) * g⁻¹ := by rw [← hv']
        _ = g * ((c * w0 * c⁻¹) * w0) * g⁻¹ := by rw [hcomm]
        _ = _ := by rw [show (g * c * g⁻¹) * (g * w0 * g⁻¹) * (g * c * g⁻¹)⁻¹ *
              (g * w0 * g⁻¹)⁻¹ = g * ((c * w0 * c⁻¹) * w0⁻¹) * g⁻¹ by group, hw2]
    show hs.proj ⟨g * v * g⁻¹, hmemN v hv g hg⟩ ∈ commW M (alternatingGroup (Fin 5)) ⊤
    rw [e1, map_mul, map_inv, ← hact]
    exact Subgroup.subset_closure ⟨b, hbA, _, Subgroup.mem_top _, rfl⟩
  have := hgen n.2
  obtain ⟨n', hn', hnn⟩ := this
  have : n' = n := Subtype.ext hnn
  rw [← this]
  exact hn'

theorem normModel_idx (hcX : c ∈ X) (hcne : ψ ⟨c, hcX⟩ ≠ 1) :
    idx (normModel hX hKd ψ hψs hker) threeCyc012 ≤ 4 := by
  have hs := isSec_normClosure hX hKd
  set M := normModel hX hKd ψ hψs hker with hM
  have ha3 : ψ ⟨c, hcX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c, hcX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hKd.c3)
    rw [this, map_one]
  obtain ⟨σ, hσ⟩ := exists_conj_threeCyc012 _ ha3 hcne
  obtain ⟨h, rfl⟩ := hψs σ
  set g' : ↥X := h * ⟨c, hcX⟩ * h⁻¹ with hg'
  have hψg' : ψ g' = threeCyc012 := by rw [hg', map_mul, map_mul, map_inv]; exact hσ
  set V' : Subgroup G := V₀.map (MulAut.conj (h : G)).toMonoidHom with hV'
  have hV'N : V' ≤ normClosure X V₀ := by
    rintro _ ⟨v, hv, rfl⟩
    exact Subgroup.subset_closure ⟨h, h.2, v, hv, rfl⟩
  have hV'card : Nat.card V' = 4 := by
    rw [hV', Subgroup.card_map_of_injective (MulAut.conj (h : G)).injective]
    exact hKd.V_card
  set S : Subgroup hs.W := (V'.subgroupOf (normClosure X V₀)).map hs.proj with hS
  have hScard : Nat.card S ≤ 4 := by
    refine (Nat.card_le_card_of_surjective _ ((hs.proj).subgroupMap_surjective _)).trans ?_
    rw [← hV'card]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV'N).toEquiv).le
  have hcomm : commW M (Subgroup.zpowers threeCyc012) ⊤ ≤ S := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨b, hb, u, -, rfl⟩
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hb)
    obtain ⟨x, rfl⟩ := hs.proj_surjective u
    have hbg : b = ψ (g' ^ m) := by rw [map_pow, hψg', hm]
    have hact := secModule_act_proj hs ψ hψs (ker_le_cSec_normClosure hX hKd ψ hψs hker)
      (g' ^ m) x
    have hxK : (x : G) ∈ K := normClosure_le_K hX hKd x.2
    have hx' : (h : G)⁻¹ * x * (h : G) ∈ K := conj_inv_mem_K hX hKd hxK h.2
    have hv := comm_pow_mem hX hKd m hx'
    have hmemV' : (h : G) * (c ^ m * ((h : G)⁻¹ * x * h) * (c ^ m)⁻¹ * ((h : G)⁻¹ * x * h)⁻¹) *
        (h : G)⁻¹ ∈ V' := ⟨_, hv, rfl⟩
    have e1 : ((hs.conjN (g' ^ m) x * x⁻¹ : ↥(normClosure X V₀)) : G) =
        (h : G) * (c ^ m * ((h : G)⁻¹ * x * h) * (c ^ m)⁻¹ * ((h : G)⁻¹ * x * h)⁻¹) *
          (h : G)⁻¹ := by
      show ((g' ^ m : ↥X) : G) * x * ((g' ^ m : ↥X) : G)⁻¹ * (x : G)⁻¹ = _
      have : ((g' ^ m : ↥X) : G) = (h : G) * c ^ m * (h : G)⁻¹ := by
        rw [hg', conj_pow]
        simp
      rw [this]; group
    refine ⟨hs.conjN (g' ^ m) x * x⁻¹, ?_, ?_⟩
    · show _ ∈ V'.subgroupOf (normClosure X V₀)
      rw [Subgroup.mem_subgroupOf, e1]; exact hmemV'
    · show hs.proj (hs.conjN (g' ^ m) x * x⁻¹) = _
      rw [map_mul, map_inv, hbg]
      exact congrArg (fun z => z * (hs.proj x)⁻¹) hact.symm
  unfold idx
  rw [bf1]
  exact (Subgroup.card_le_of_le hcomm).trans hScard

theorem psi_c_ne_one (hK2 : IsPGroup 2 K) (hcX : c ∈ X) : ψ ⟨c, hcX⟩ ≠ 1 := by
  intro h1
  have hcK : c ∈ K := (hker _).mp h1
  obtain ⟨k, hk⟩ := hK2 ⟨c, hcK⟩
  have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 := hKd.c3
  have : c = 1 := by
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have := (pow_gcd_eq_one (a := c)).mpr ⟨hk', h3⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  exact hKd.cne this

theorem normModel_iso_orth (hK2 : IsPGroup 2 K) (hcX : c ∈ X) :
    Nonempty ((normModel hX hKd ψ hψs hker).Iso orth) :=
  model_iso_orth _ (normModel_nontrivial hX hKd ψ hψs hker)
    (normModel_idx hX hKd ψ hψs hker hcX (psi_c_ne_one hX hKd ψ hψs hker hK2 hcX))
    (normModel_comm hX hKd ψ hψs hker hcX)

theorem isOrthSec_normClosure (hK2 : IsPGroup 2 K) (hcX : c ∈ X) :
    IsOrthSec X ⊥ (normClosure X V₀) := by
  obtain ⟨e⟩ := normModel_iso_orth hX hKd ψ hψs hker hK2 hcX
  have hfaith := Model.Faithful.of_iso e orth_faithful
  have hk := ker_le_cSec_normClosure hX hKd ψ hψs hker
  have hker' : ψ.ker = (cSecIn X ⊥ (normClosure X V₀)).subgroupOf X :=
    le_antisymm hk ((secModule_faithful_iff (isSec_normClosure hX hKd) ψ hψs hk).mp hfaith)
  exact isModelSec_of_iso (isSec_normClosure hX hKd) ψ hψs hker' e.symm

end Bridge

end CFSG.Quasithin.F53
