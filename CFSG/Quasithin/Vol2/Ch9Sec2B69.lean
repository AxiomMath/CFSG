module

public import CFSG.Quasithin.Vol2.Ch3yB69

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
  CFSG.Quasithin.D15Proof
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isElemAbelian2_autOn_secImg_of_comm {K E B : Subgroup G}
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K E))
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' * b⁻¹ * b'⁻¹ ∈ Subgroup.centralizer (E : Set G))
    (hBs : ∀ b ∈ B, b ^ 2 ∈ Subgroup.centralizer (E : Set G)) :
    @IsElemAbelian2 ↥(secImg (Subgroup.normalizer (K : Set G)) K E) (commGroupOfElemAbelian hE)
      (autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
        (secImg (Subgroup.normalizer (K : Set G)) K E)) := by
  set A := Subgroup.normalizer (K : Set G) with hA
  set Et := secImg A K E with hEt
  have triv : ∀ (g : Subgroup.normalizer (Et : Set (SecQuot A K))) (c : A),
      (c : G) ∈ Subgroup.centralizer (E : Set G) → (g : SecQuot A K) = secMk A K c →
      conjAct Et g = 1 := by
    intro g c hc hg
    rw [A4.conjAct_eq_one_iff, hg, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨e, he, rfl⟩ := mem_secImg.mp hy
    refine secMk_comm_of_commutator_mem ?_
    have hce : (e : G) * c = c * e := Subgroup.mem_centralizer_iff.mp hc e he
    rw [hce, mul_inv_cancel_right, mul_inv_cancel]
    exact K.one_mem
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨g, hgB, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨h, hhB, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨b, hb, hbg⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hgB)
    obtain ⟨b', hb', hbh⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hhB)
    have h1 : conjAct Et (g * h * g⁻¹ * h⁻¹) = 1 :=
      triv _ (b * b' * b⁻¹ * b'⁻¹) (by simpa using hBc b hb b' hb')
        (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inv, ← hbg, ← hbh]; simp only [map_mul, map_inv]; rfl)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc conjAct Et g * conjAct Et h
        = (conjAct Et g * conjAct Et h * (conjAct Et g)⁻¹ * (conjAct Et h)⁻¹) *
            (conjAct Et h * conjAct Et g) := by group
      _ = conjAct Et h * conjAct Et g := by rw [h1, one_mul]
  · obtain ⟨g, hgB, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, hbg⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hgB)
    rw [← map_pow]
    exact triv _ (b ^ 2) (by simpa using hBs b hb)
      (by rw [Subgroup.coe_pow, ← hbg]; simp only [map_pow]; rfl)

variable [Finite G]

theorem isStrongFFModule_autOn_secImg_of_comm {K E X' B : Subgroup G}
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K E))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hX'K : X' ≤ Subgroup.normalizer (K : Set G))
    (hX'E : X' ≤ Subgroup.normalizer (E : Set G)) (hBX' : B ≤ X')
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' * b⁻¹ * b'⁻¹ ∈ Subgroup.centralizer (E : Set G))
    (hBs : ∀ b ∈ B, b ^ 2 ∈ Subgroup.centralizer (E : Set G))
    (hnt : ¬ ∀ b ∈ B, ∀ e ∈ E, b * e * b⁻¹ * e⁻¹ ∈ K)
    (hlt : (centralizerMod K E B).relIndex E < (centralizerMod K B E).relIndex B) :
    @IsStrongFFModule ↥(secImg (Subgroup.normalizer (K : Set G)) K E) (commGroupOfElemAbelian hE)
      (autOn (secImg (Subgroup.normalizer (K : Set G)) K X')
        (secImg (Subgroup.normalizer (K : Set G)) K E)) := by
  let _ : CommGroup ↥(secImg (Subgroup.normalizer (K : Set G)) K E) := commGroupOfElemAbelian hE
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := hBX'.trans hX'K
  have hBE : B ≤ Subgroup.normalizer (E : Set G) := hBX'.trans hX'E
  have hn := secImg_le_normalizer_secImg (K := K) (E := E) (X := B) hBE
  refine ⟨autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
    (secImg (Subgroup.normalizer (K : Set G)) K E),
    autOn_le_autOn _ (secImg_mono hBX'), ?_, isElemAbelian2_autOn_secImg_of_comm hE hBc hBs,
    ?_⟩
  · refine autOn_ne_bot_of_not_le_centralizer hn ?_
    intro hle'
    apply hnt
    intro b hb e he
    have := Subgroup.mem_centralizer_iff.mp
      (hle' (secMk_mem_secImg (x := ⟨b, hBK hb⟩) hb))
      (secMk (Subgroup.normalizer (K : Set G)) K ⟨e, hEK he⟩)
      (secMk_mem_secImg (x := ⟨e, hEK he⟩) he)
    exact commutator_mem_of_secMk_commute (x := ⟨b, hBK hb⟩) (y := ⟨e, hEK he⟩) this.symm
  · have c1 := card_autOn_secImg hBK hEK hBE
    have c2 := card_fixV_autOn_eq hE hn
    have c3 := relIndex_secImg_fix (K := K) (E := E) (X := B) hBK hEK
    have hmul := Subgroup.relIndex_mul_card
      (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
        (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K)))
      (secImg (Subgroup.normalizer (K : Set G)) K E)
    rw [inf_eq_left.mpr inf_le_left] at hmul
    have hpos : 0 < Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓
        Subgroup.centralizer (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := Nat.card_pos
    rw [c1, c2]
    calc Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E)
        = (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))).relIndex
            (secImg (Subgroup.normalizer (K : Set G)) K E) *
          Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := hmul.symm
      _ < (centralizerMod K B E).relIndex B *
          Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := by
        rw [c3]; exact Nat.mul_lt_mul_of_pos_right hlt hpos

theorem relIndex_le_of_b69One (hB : B69One) {G₂ T M₂ U K : Subgroup G}
    (hmp : MinParabolic G₂ T M₂) (hsqtk : IsSQTKSub G₂) (hUe : IsElemAbelian 2 U) (hKU : K ≤ U)
    (hG₂K : G₂ ≤ Subgroup.normalizer (K : Set G)) (hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G))
    (hCM : centralizerMod K G₂ U ≤ M₂)
    (hred : ∀ D : Subgroup G, D ≤ G₂ → G₂ ≤ Subgroup.normalizer (D : Set G) →
      (∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ centralizerMod K G₂ U) → D ≤ centralizerMod K G₂ U)
    {P : Subgroup G} (hPG : P ≤ G₂)
    (hPc : ∀ b ∈ P, ∀ b' ∈ P, b * b' * b⁻¹ * b'⁻¹ ∈ Subgroup.centralizer (U : Set G))
    (hPs : ∀ b ∈ P, b ^ 2 ∈ Subgroup.centralizer (U : Set G)) :
    (centralizerMod K P U).relIndex P ≤ (centralizerMod K U P).relIndex U := by
  have hUc := (B6.isElemAbelian_iff.mp hUe).1
  have hUK : U ≤ Subgroup.normalizer (K : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hKU]
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    have e : ((g * k * g⁻¹ : ↥U) : G) = k := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hUc g g.2 k k.2, mul_inv_cancel_right]
    rw [e]
    exact hk
  have hE := isElemAbelian_secImg_of_le (L := K) hUe (le_refl U)
  by_contra hlt
  push Not at hlt
  have hnt : ¬ ∀ b ∈ P, ∀ e ∈ U, b * e * b⁻¹ * e⁻¹ ∈ K := by
    intro hall
    have hCA : centralizerMod K P U = P := le_antisymm (centralizerMod_le_left _ _ _)
      fun b hb => ⟨hb, hG₂K (hPG hb), hall b hb⟩
    rw [hCA, Subgroup.relIndex_self] at hlt
    exact absurd hlt (not_lt.mpr (Nat.one_le_iff_ne_zero.mpr (relIndex_ne_zero _ _)))
  have hStrong := isStrongFFModule_autOn_secImg_of_comm hE hUK hG₂K hG₂U hPG hPc hPs hnt hlt
  set A_ := Subgroup.normalizer (K : Set G) with hAdef
  set E := secImg A_ K U with hEdef
  set X := autOn (secImg A_ K G₂) E with hXdef
  let _ : CommGroup ↥E := commGroupOfElemAbelian hE
  have hsq' : ∀ v : ↥E, v ^ 2 = 1 := fun v => Subtype.ext (hE.2 v v.2)
  have hmemE : ∀ g : ↥G₂, secMk A_ K (Subgroup.inclusion hG₂K g) ∈
      Subgroup.normalizer (E : Set (SecQuot A_ K)) := fun g =>
    secMk_mem_normalizer_secImg (hG₂U g.2)
  let β : ↥G₂ →* ↥(Subgroup.normalizer (E : Set (SecQuot A_ K))) :=
    ((secMk A_ K).comp (Subgroup.inclusion hG₂K)).codRestrict _ hmemE
  let ψ : ↥G₂ →* MulAut ↥E := (conjAct E).comp β
  have hψX : ∀ g : ↥G₂, ψ g ∈ X := fun g =>
    Subgroup.mem_map.mpr ⟨β g, Subgroup.mem_subgroupOf.mpr
      (secMk_mem_secImg (A := A_) (B := K) (X := G₂) (x := Subgroup.inclusion hG₂K g) g.2), rfl⟩
  let φ : ↥G₂ →* ↥X := ψ.codRestrict X hψX
  have hφsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨a, haG, hay⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨⟨a, haG⟩, Subtype.ext ?_⟩
    show conjAct E (β ⟨a, haG⟩) = conjAct E y
    congr 1
    exact Subtype.ext hay
  have hker1 : ∀ g : ↥G₂, φ g = 1 ↔ (g : G) ∈ centralizerMod K G₂ U := by
    intro g
    constructor
    · intro hg
      have hψ1 : ψ g = 1 := congrArg Subtype.val hg
      have hcent : ((β g : ↥(Subgroup.normalizer (E : Set (SecQuot A_ K)))) : SecQuot A_ K) ∈
          Subgroup.centralizer (E : Set (SecQuot A_ K)) := A4.conjAct_eq_one_iff.mp hψ1
      refine ⟨g.2, hG₂K g.2, fun n hn => ?_⟩
      have hnE : secMk A_ K ⟨n, hUK hn⟩ ∈ E := secMk_mem_secImg (A := A_) (B := K) (X := U) hn
      have hcomm := Subgroup.mem_centralizer_iff.mp hcent _ hnE
      have h1 : secMk A_ K (⟨g, hG₂K g.2⟩ * ⟨n, hUK hn⟩ * ⟨g, hG₂K g.2⟩⁻¹ * ⟨n, hUK hn⟩⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        have hc : secMk A_ K ⟨n, hUK hn⟩ * secMk A_ K ⟨g, hG₂K g.2⟩ =
            secMk A_ K ⟨g, hG₂K g.2⟩ * secMk A_ K ⟨n, hUK hn⟩ := hcomm
        rw [← hc]
        group
      exact secMk_eq_one_iff.mp h1
    · intro hg
      refine Subtype.ext (A4.conjAct_eq_one_iff.mpr (Subgroup.mem_centralizer_iff.mpr ?_))
      intro y hy
      obtain ⟨e, he, rfl⟩ := mem_secImg.mp hy
      exact (secMk_comm_of_commutator_mem (x := ⟨(g : G), hG₂K g.2⟩) (y := e)
        (hg.2.2 e he)).symm
  have hker : φ.ker ≤ M₂.subgroupOf G₂ := fun g hg =>
    Subgroup.mem_subgroupOf.mpr (hCM ((hker1 g).mp hg))
  have hmpX := MinParabolic.map_of_surjective hmp.subgroupOf hφsurj hker
  have hO2 : pCoreOf 2 (⊤ : Subgroup ↥X) = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set Qx : Subgroup ↥X := pCoreOf 2 (⊤ : Subgroup ↥X) with hQxdef
    have hQn : Qx.Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_pCoreOf 2 (⊤ : Subgroup ↥X)))
    have hQ2 : IsPGroup 2 Qx := pCoreOf_isPGroup 2 _
    set D : Subgroup G := (Qx.comap φ).map G₂.subtype with hDdef
    have hDsub : D.subgroupOf G₂ = Qx.comap φ :=
      Subgroup.comap_map_eq_self_of_injective G₂.subtype_injective _
    have hDG : D ≤ G₂ := Subgroup.map_subtype_le _
    have hDn : G₂ ≤ Subgroup.normalizer (D : Set G) := by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hDG, hDsub]
      exact hQn.comap φ
    have hDC := hred D hDG hDn fun d hd => by
      obtain ⟨x, hx, rfl⟩ := hd
      obtain ⟨k, hk⟩ := hQ2 ⟨φ x, hx⟩
      have hk' : φ (x ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      exact ⟨k, by simpa using (hker1 _).mp hk'⟩
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨x, rfl⟩ := hφsurj y
    have hxD : (x : G) ∈ D := ⟨x, hy, rfl⟩
    exact Subgroup.mem_bot.mpr ((hker1 x).mpr (hDC hxD))
  exact hB E hsq' X _ _ ⟨↥G₂, inferInstance, inferInstance, hsqtk.2, hsqtk.1, φ, hφsurj⟩ hmpX hO2
    hStrong

end CFSG.Quasithin.H13.Ch9
