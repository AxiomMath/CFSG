module

public import CFSG.Quasithin.EmptyFaithful.SzPS8Lift
public import CFSG.Quasithin.EmptyFaithful.SzPS8Kbar
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Insp
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.Quasithin.EmptyFaithful.SzN28PDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R CFSG.LieType.BorelTits
  CFSG.Quasithin.G11
open scoped MatrixGroups

namespace SzPS8

section Rho

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

@[expose] noncomputable def rhoOn (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M)
    {L : Subgroup G} (hLH : L ≤ mcOf T) {Kd : Subgroup ↥(D.img (mcOf T))}
    (hLρ : (L.subgroupOf (mcOf T)).map (rhoΓ h D) = Kd) : ↥L →* ↥Kd :=
  ((rhoΓ h D).comp (Subgroup.inclusion hLH)).codRestrict Kd (fun x => by
    rw [← hLρ]
    exact ⟨Subgroup.inclusion hLH x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)

theorem rhoOn_surjective (h : Hyp1281Two G T M (yOfL22 T M)) (D : HatModel T M)
    {L : Subgroup G} (hLH : L ≤ mcOf T) {Kd : Subgroup ↥(D.img (mcOf T))}
    (hLρ : (L.subgroupOf (mcOf T)).map (rhoΓ h D) = Kd) :
    Function.Surjective (rhoOn h D hLH hLρ) := by
  rintro ⟨k, hk⟩
  rw [← hLρ] at hk
  obtain ⟨y, hy, rfl⟩ := hk
  exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, Subtype.ext rfl⟩

end Rho

section Kbar

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem kbar_of_lift (hyp : Hyp1421 G T M) (h11 : StageLemma14111) (h113 : StageLemma14113)
    (h36 : A36ForSQTK) (D : HatModel T M) {Kd : Subgroup ↥(D.img (mcOf T))}
    (hKs : IsSimpleGroup ↥Kd) (e : ↥Kd ≃* SL(2, L28.F8)) {L : Subgroup G}
    (hL : L ∈ cComp (mcOf T))
    (hLρ : (L.subgroupOf (mcOf T)).map (rhoΓ (hyp.hyp1281Two_of_inputs h11 h113) D) = Kd) :
    (∀ x : ↥(mcOf T), (x : G) ∈ L → rhoΓ (hyp.hyp1281Two_of_inputs h11 h113) D x = 1 →
        (x : G) ∈ pCoreOf 2 L) ∧ Nonempty (KBar L ≃* ↥Kd) := by
  classical
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  have hH : pCoreOf 2 (mcOf T) ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hyp.mc_max.1
  have hLH : L ≤ mcOf T := le_of_mem_cComp hL
  let χ : ↥L →* ↥Kd := rhoOn h1281 D hLH hLρ
  have hχ : Function.Surjective χ := rhoOn_surjective h1281 D hLH hLρ
  obtain ⟨ψ, hψ, hψker⟩ := exists_modO2_surjection hL
  have hψ2 : IsPGroup 2 ψ.ker := hψker ▸ CFSG.pCore_isPGroup
  have hX : CFSG.IsQuasisimple ↥(modO2Image (mcOf T) L) ∨
      A36Case3 ↥(modO2Image (mcOf T) L) ∨ A36Case4 ↥(modO2Image (mcOf T) L) := by
    have hstrong := lemma_1_2_1_four_strong hyp.qtke hyp.simple hyp.nonabelian h36 hH hL
    rcases hstrong.1 with ⟨hc, -⟩ | ⟨hc, -⟩ | h3 | h4
    · exact Or.inl hc.1
    · exact Or.inl hc.1
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h4)
  have hle : ψ.ker ≤ χ.ker := by
    rw [hψker]
    intro x hx
    have hxG : (x : G) ∈ pCoreOf 2 L := by
      exact ⟨x, hx, rfl⟩
    have hxH : (x : G) ∈ pCoreOf 2 (mcOf T) :=
      A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hL) hxG
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact rhoΓ_eq_one_of_mem_pCoreOf h1281 D (x := Subgroup.inclusion hLH x) hxH
  have hker2 : IsPGroup 2 χ.ker := isPGroup_ker_of_a36_lift hX hKs e ψ hψ hψ2 χ hχ hle
  have hkerle : χ.ker ≤ CFSG.pCore 2 ↥L := le_sSup ⟨inferInstance, hker2⟩
  have hkerEq : χ.ker = CFSG.pCore 2 ↥L := le_antisymm hkerle (by rw [← hψker]; exact hle)
  have hsub : (pCoreOf 2 L).subgroupOf L = χ.ker := by
    rw [hkerEq]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  refine ⟨fun x hxL hx1 => ?_, ⟨?_⟩⟩
  · have hmem : (⟨(x : G), hxL⟩ : ↥L) ∈ χ.ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact hx1
    rw [← hsub] at hmem
    exact hmem
  · exact (QuotientGroup.quotientMulEquivOfEq hsub).trans
      (QuotientGroup.quotientKerEquivOfSurjective χ hχ)

end Kbar

section Borel

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem borel_le_M (hyp : Hyp1421 G T M) (h11 : StageLemma14111) (h113 : StageLemma14113)
    (D : HatModel T M) {Kd : Subgroup ↥(D.img (mcOf T))} (hKn : Kd.Normal)
    (e : ↥Kd ≃* SL(2, L28.F8)) {L : Subgroup G} (hL : L ∈ cComp (mcOf T))
    (hTN : T ≤ Subgroup.normalizer (L : Set G))
    (hLρ : (L.subgroupOf (mcOf T)).map (rhoΓ (hyp.hyp1281Two_of_inputs h11 h113) D) = Kd)
    (hker : ∀ x : ↥(mcOf T), (x : G) ∈ L →
      rhoΓ (hyp.hyp1281Two_of_inputs h11 h113) D x = 1 → (x : G) ∈ pCoreOf 2 L) :
    L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ M := by
  classical
  have h1281 : Hyp1281Two G T M (yOfL22 T M) := hyp.hyp1281Two_of_inputs h11 h113
  set ρ := rhoΓ h1281 D with hρ
  have hLH : L ≤ mcOf T := le_of_mem_cComp hL
  have hTH : T ≤ mcOf T := h1281.almostSpecialHyp_g1.T_le_H
  have hsylLT : IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
  have hLc : L ∈ cComp (L ⊔ T) := cComp_mem_of_le hL le_sup_left (sup_le hLH hTH)
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hLc) hsylLT
  have hpc : pCoreOf 2 L ≤ T ⊓ L := pCoreOf_two_le_of_isSylowTwoOf hsylL
  set S : Subgroup G := T ⊓ L with hS
  have hSL : S ≤ L := inf_le_right
  have hST : S ≤ T := inf_le_left
  have hTL : ∀ t ∈ T, ∀ x, x ∈ L ↔ t * x * t⁻¹ ∈ L := fun t ht =>
    Subgroup.mem_normalizer_iff.mp (hTN ht)
  have hSnorm : ∀ t ∈ T, ∀ s ∈ S, t * s * t⁻¹ ∈ S := fun t ht s hs =>
    ⟨T.mul_mem (T.mul_mem ht (hST hs)) (T.inv_mem ht), (hTL t ht s).mp (hSL hs)⟩
  have := hKn
  let χ : ↥L →* ↥Kd := rhoOn h1281 D hLH hLρ
  have hχ : Function.Surjective χ := rhoOn_surjective h1281 D hLH hLρ
  let P₀ : Subgroup ↥Kd := (S.subgroupOf L).map χ
  let P : Subgroup ↥(D.img (mcOf T)) := P₀.map Kd.subtype
  have hPK : P ≤ Kd := Subgroup.map_subtype_le P₀
  have hPsub : P.subgroupOf Kd = P₀ :=
    Subgroup.comap_map_eq_self_of_injective Kd.subtype_injective P₀
  have hS2 : IsPGroup 2 ↥(S.subgroupOf L) :=
    hsylL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  have hP2 : IsPGroup 2 P := (hS2.map χ).map Kd.subtype
  have hPidx : ¬ 2 ∣ (P.subgroupOf Kd).index := by
    rw [hPsub]
    intro hd
    exact hsylL.2.2 (hd.trans (Subgroup.index_map_dvd (S.subgroupOf L) hχ))
  have hPmem : ∀ (s : G) (hs : s ∈ S), ρ (Subgroup.inclusion hLH ⟨s, hSL hs⟩) ∈ P := by
    intro s hs
    exact ⟨χ ⟨s, hSL hs⟩, ⟨⟨s, hSL hs⟩, hs, rfl⟩, rfl⟩
  have hPex : ∀ y ∈ P, ∃ s : ↥L, (s : G) ∈ S ∧ ρ (Subgroup.inclusion hLH s) = y := by
    rintro y ⟨k, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  have hconj : ∀ u : ↥(mcOf T), (∀ s ∈ S, (u : G) * s * (u : G)⁻¹ ∈ S) →
      ∀ p ∈ P, ρ u * p * (ρ u)⁻¹ ∈ P := by
    intro u hu p hp
    obtain ⟨s, hsS, rfl⟩ := hPex p hp
    have hs' := hu (s : G) hsS
    have h1 : ρ u * ρ (Subgroup.inclusion hLH s) * (ρ u)⁻¹ =
        ρ (Subgroup.inclusion hLH ⟨(u : G) * s * (u : G)⁻¹, hSL hs'⟩) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [h1]
    exact hPmem _ hs'
  have hBS : ∀ b : G, b ∈ L → b ∈ Subgroup.normalizer (S : Set G) →
      ∀ t ∈ T, b * t * b⁻¹ ∈ T := by
    intro b hbL hbN t htT
    have htH : t ∈ mcOf T := hTH htT
    have hbH : b ∈ mcOf T := hLH hbL
    obtain ⟨m, hm⟩ := hsylLT.2.1 ⟨t, htT⟩
    have hm' : t ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have hγm : (ρ ⟨t, htH⟩) ^ 2 ^ m = 1 := by
      rw [← map_pow]
      have : (⟨t, htH⟩ : ↥(mcOf T)) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm')
      rw [this, map_one]
    have htinv : ρ ⟨t⁻¹, hTH (T.inv_mem htT)⟩ = (ρ ⟨t, htH⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    have hγP : ∀ p, p ∈ P ↔ ρ ⟨t, htH⟩ * p * (ρ ⟨t, htH⟩)⁻¹ ∈ P := by
      intro p
      constructor
      · exact hconj ⟨t, htH⟩ (fun s hs => hSnorm t htT s hs) p
      · intro hp
        have := hconj ⟨t⁻¹, hTH (T.inv_mem htT)⟩
          (fun s hs => by simpa using hSnorm t⁻¹ (T.inv_mem htT) s hs) _ hp
        rw [htinv] at this
        simpa [mul_assoc] using this
    have hbnorm : ∀ s ∈ S, b * s * b⁻¹ ∈ S := fun s hs =>
      (Subgroup.mem_normalizer_iff.mp hbN s).mp hs
    have hbnorm' : ∀ s ∈ S, b⁻¹ * s * b ∈ S := fun s hs => by
      refine (Subgroup.mem_normalizer_iff.mp hbN (b⁻¹ * s * b)).mpr ?_
      simpa [mul_assoc] using hs
    have hbinv : ρ ⟨b⁻¹, hLH (L.inv_mem hbL)⟩ = (ρ ⟨b, hbH⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    have hkP : ρ ⟨b, hbH⟩ ∈ Subgroup.normalizer (P : Set ↥(D.img (mcOf T))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro p
      constructor
      · exact hconj ⟨b, hbH⟩ hbnorm p
      · intro hp
        have := hconj ⟨b⁻¹, hLH (L.inv_mem hbL)⟩ (fun s hs => by simpa using hbnorm' s hs) _ hp
        rw [hbinv] at this
        simpa [mul_assoc] using this
    have hkK : ρ ⟨b, hbH⟩ ∈ Kd := (χ ⟨b, hbL⟩).2
    have hmain := L28.borel_comm e hPK hP2 hPidx m hγm hγP hkP hkK
    set xH : ↥(mcOf T) := ⟨b, hbH⟩ * (⟨t, htH⟩ * ⟨b, hbH⟩⁻¹ * ⟨t, htH⟩⁻¹) with hxH
    have hxG : (xH : G) = b * (t * b⁻¹ * t⁻¹) := by simp [hxH]
    have hρx : ρ xH ∈ P := by
      rw [hxH, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hmain
    have hxL : (xH : G) ∈ L := by
      rw [hxG]
      refine L.mul_mem hbL ?_
      have h1 : t * b⁻¹ * t⁻¹ ∈ L := (hTL t htT b⁻¹).mp (L.inv_mem hbL)
      simpa [mul_assoc] using h1
    obtain ⟨s, hsS, hsx⟩ := hPex _ hρx
    have hker1 : ρ (xH⁻¹ * Subgroup.inclusion hLH s) = 1 := by
      rw [map_mul, map_inv, hsx, inv_mul_cancel]
    have hmemL : ((xH⁻¹ * Subgroup.inclusion hLH s : ↥(mcOf T)) : G) ∈ L := by
      have : ((xH⁻¹ * Subgroup.inclusion hLH s : ↥(mcOf T)) : G) = (xH : G)⁻¹ * (s : G) := rfl
      rw [this]
      exact L.mul_mem (L.inv_mem hxL) s.2
    have hO := hker _ hmemL hker1
    have hxs : (xH : G)⁻¹ * (s : G) ∈ S := hpc hO
    have hxS : (xH : G) ∈ S := by
      have h1 : (xH : G)⁻¹ ∈ S := by
        have := S.mul_mem hxs (S.inv_mem hsS)
        simpa using this
      simpa using S.inv_mem h1
    have hbt : b * t * b⁻¹ = (xH : G) * t := by
      rw [hxG]
      group
    rw [hbt]
    exact T.mul_mem (hST hxS) htT
  intro b hb
  obtain ⟨hbL, hbN⟩ := hb
  have hbT : b ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      exact hBS b hbL hbN t ht
    · intro ht
      have hbinvN : b⁻¹ ∈ Subgroup.normalizer (S : Set G) := (Subgroup.normalizer _).inv_mem hbN
      have := hBS b⁻¹ (L.inv_mem hbL) hbinvN _ ht
      simpa [mul_assoc] using this
  exact (hyp.normalizer_le hbT).1

end Borel

section Main

theorem excl11 (h11 : StageLemma14111) (h113 : StageLemma14113) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h39 : A39ForSQTK) (hE22 : E2.E22StatementNoN) (hF : FieldOne1432) :
    Lemma14315Excl11 := by
  intro G _ _ T M hyp hnot hnab D hc
  exfalso
  obtain ⟨hsimp, hcard⟩ := H13.L1294I.fstar_of_concl11 hc
  obtain ⟨-, ⟨e⟩⟩ := hc
  have hKn : (genFittingFStar ↥(D.img (mcOf T))).Normal :=
    CFSG.ClassicalInvolution.genFittingFStar_normal _
  have hKnc : ¬ IsMulCommutative ↥(genFittingFStar ↥(D.img (mcOf T))) := fun hcomm => by
    obtain ⟨a, b, hab⟩ := nonab_of_card_ordL2 hsimp (m := 3) (by norm_num)
      (by rw [hcard]; norm_num [ordL2])
    exact hab (hcomm.is_comm.comm a b)
  refine false_of_normal_component hyp hnot hnab h11 h113 h37 h39 hE22 hF D hKn hsimp hKnc
    (m := 3) (by norm_num) (fun L hL hTN hLρ => ?_)
  obtain ⟨hker, ⟨eK⟩⟩ := kbar_of_lift hyp h11 h113 h36 D hsimp e hL hLρ
  refine ⟨eK.isSimpleGroup, fusionIsBenderGroup_of_sl2_f8 (eK.trans e), ?_,
    borel_le_M hyp h11 h113 D hKn e hL hTN hLρ hker⟩
  rw [Nat.card_congr eK.toEquiv, hcard]
  norm_num [ordL2]

end Main

end SzPS8

end CFSG.Quasithin
