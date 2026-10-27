module

public import CFSG.Quasithin.EmptyFaithful.S146zClaim

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Glue

variable {G : Type} [Group G] [Finite G] {T M K Kp : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

omit [Finite G] in
theorem mem_normalizer_commutator_sup {a : G} (haK : a ∈ Subgroup.normalizer (K : Set G))
    (haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (haZ : a ∈ Subgroup.normalizer (Zz : Set G)) :
    a ∈ Subgroup.normalizer ((⁅uOfL22 T M, K⁆ ⊔ Zz : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjSub_eq
  rw [conjSub_sup, conjSub_commutator', conjSub_eq_of_mem_normalizer haU,
    conjSub_eq_of_mem_normalizer haK, conjSub_eq_of_mem_normalizer haZ]

omit [Finite G] in
theorem commutator_sup_le_U (hKH : K ≤ mcOf T) : ⁅uOfL22 T M, K⁆ ⊔ Zz ≤ uOfL22 T M :=
  sup_le (S145.commutator_le_of_le_normalizer (hKH.trans (le_normalizer_conjClosure _ _)))
    (Z_le_conjClosure_VZ T M (mcOf T))

theorem exists_decomp_two (S : Setting146 G T M) (hc23 : Conc14623 T M)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) (hK : K ∈ cComp (mcOf T))
    (hKp : Kp ∈ cComp (mcOf T)) {v : G} (hv : v ∈ uOfL22 T M) :
    ∃ a ∈ ⁅uOfL22 T M, K⁆ ⊔ Zz, ∃ b ∈ ⁅uOfL22 T M, Kp⁆ ⊔ Zz, ∃ c ∈ cuOf T M,
      v = a * (b * c) := by
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) :=
    S.conjClosure_le_normalizer_Z S.isHTM_mcOf
  have hUKU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hK)
  have hUpU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hKp)
  have h3 := hc23.2.2.1
  have hle1 : (⨆ K' ∈ cComp (mcOf T), tildeOf Zz ⁅uOfL22 T M, K'⁆) ≤
      tildeOf Zz ((⁅uOfL22 T M, K⁆ ⊔ Zz) ⊔ (⁅uOfL22 T M, Kp⁆ ⊔ Zz)) := by
    refine iSup₂_le fun K' hK' => ?_
    rcases hcomps K' hK' with h | h
    · rw [h]
      exact secImg_mono (le_sup_left.trans le_sup_left)
    · rw [h]
      exact secImg_mono (le_sup_left.trans le_sup_right)
  have hU12 : (⁅uOfL22 T M, K⁆ ⊔ Zz) ⊔ (⁅uOfL22 T M, Kp⁆ ⊔ Zz) ≤ Subgroup.normalizer (Zz : Set G) :=
    (sup_le hUKU hUpU).trans hUN
  have hcuN : cuOf T M ≤ Subgroup.normalizer (Zz : Set G) := (cuOf_le T M).trans hUN
  have h4 : tildeOf Zz (uOfL22 T M) ≤
      tildeOf Zz (((⁅uOfL22 T M, K⁆ ⊔ Zz) ⊔ (⁅uOfL22 T M, Kp⁆ ⊔ Zz)) ⊔ cuOf T M) := by
    rw [tildeOf_sup hU12 hcuN, h3]
    exact sup_le_sup_right hle1 _
  have hvN : v ∈ Subgroup.normalizer (Zz : Set G) := hUN hv
  have hZ12 : Zz ≤ ((⁅uOfL22 T M, K⁆ ⊔ Zz) ⊔ (⁅uOfL22 T M, Kp⁆ ⊔ Zz)) ⊔ cuOf T M :=
    le_sup_right.trans (le_sup_left.trans le_sup_left)
  have h5 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨v, hvN⟩ ∈
      tildeOf Zz (((⁅uOfL22 T M, K⁆ ⊔ Zz) ⊔ (⁅uOfL22 T M, Kp⁆ ⊔ Zz)) ⊔ cuOf T M) :=
    h4 (secMk_mem_secImg (x := ⟨v, hvN⟩) hv)
  have h6 : v ∈ ((⁅uOfL22 T M, K⁆ ⊔ Zz) ⊔ (⁅uOfL22 T M, Kp⁆ ⊔ Zz)) ⊔ cuOf T M :=
    (secMk_mem_secImg_iff (x := ⟨v, hvN⟩) hZ12).mp h5
  have hcomm12 : ∀ a ∈ (⁅uOfL22 T M, K⁆ ⊔ Zz) ⊔ (⁅uOfL22 T M, Kp⁆ ⊔ Zz), ∀ b ∈ cuOf T M,
      a * b = b * a := fun a ha b hb =>
    S.comm_of_mem_conjClosure (sup_le hUKU hUpU ha) (cuOf_le T M hb)
  have hN12 : (⁅uOfL22 T M, K⁆ ⊔ Zz) ⊔ (⁅uOfL22 T M, Kp⁆ ⊔ Zz) ≤
      Subgroup.normalizer ((cuOf T M : Subgroup G) : Set G) :=
    le_normalizer_of_forall_commute hcomm12
  have h7 : v ∈ ((((⁅uOfL22 T M, K⁆ ⊔ Zz) ⊔ (⁅uOfL22 T M, Kp⁆ ⊔ Zz)) ⊔ cuOf T M :
      Subgroup G) : Set G) := h6
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN12] at h7
  obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.mp h7
  have hN₁₂ : ⁅uOfL22 T M, K⁆ ⊔ Zz ≤ Subgroup.normalizer ((⁅uOfL22 T M, Kp⁆ ⊔ Zz : Subgroup G) : Set G) :=
    le_normalizer_of_forall_commute fun x hx y hy =>
      S.comm_of_mem_conjClosure (hUKU hx) (hUpU hy)
  have ha' : a ∈ (((⁅uOfL22 T M, K⁆ ⊔ Zz) ⊔ (⁅uOfL22 T M, Kp⁆ ⊔ Zz) : Subgroup G) : Set G) := ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN₁₂] at ha'
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Set.mem_mul.mp ha'
  exact ⟨y₁, hy₁, y₂, hy₂, d, hd, by group⟩

theorem inf_eq_Z_two (S : Setting146 G T M) (hc23 : Conc14623 T M) (hK : K ∈ cComp (mcOf T))
    (hKp : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K) :
    (⁅uOfL22 T M, K⁆ ⊔ Zz) ⊓ (⁅uOfL22 T M, Kp⁆ ⊔ Zz) = Zz := by
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) :=
    S.conjClosure_le_normalizer_Z S.isHTM_mcOf
  have hUKU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hK)
  have hUpU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hKp)
  apply le_antisymm
  · rintro x ⟨hxK, hxp⟩
    have hxU : x ∈ uOfL22 T M := hUKU hxK
    have hxN : x ∈ Subgroup.normalizer (Zz : Set G) := hUN hxU
    have hKN : ⁅uOfL22 T M, K⁆ ≤ Subgroup.normalizer (Zz : Set G) :=
      (le_sup_left.trans hUKU).trans hUN
    have hKpN : ⁅uOfL22 T M, Kp⁆ ≤ Subgroup.normalizer (Zz : Set G) :=
      (le_sup_left.trans hUpU).trans hUN
    have h1 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨x, hxN⟩ ∈
        tildeOf Zz (⁅uOfL22 T M, K⁆ ⊔ Zz) := secMk_mem_secImg (x := ⟨x, hxN⟩) hxK
    have h2 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨x, hxN⟩ ∈
        tildeOf Zz (⁅uOfL22 T M, Kp⁆ ⊔ Zz) := secMk_mem_secImg (x := ⟨x, hxN⟩) hxp
    rw [tildeOf_sup_self hKN] at h1
    rw [tildeOf_sup_self hKpN] at h2
    have h3 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨x, hxN⟩ ∈
        ⨆ K'' ∈ {K'' | K'' ∈ cComp (mcOf T) ∧ K'' ≠ K}, tildeOf Zz ⁅uOfL22 T M, K''⁆ :=
      (le_iSup₂ (f := fun K'' (_ : K'' ∈ {K'' | K'' ∈ cComp (mcOf T) ∧ K'' ≠ K}) =>
        tildeOf Zz ⁅uOfL22 T M, K''⁆) Kp ⟨hKp, hne⟩) h2
    have h4 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨x, hxN⟩ ∈
        tildeOf Zz ⁅uOfL22 T M, K⁆ ⊓
          (⨆ K'' ∈ {K'' | K'' ∈ cComp (mcOf T) ∧ K'' ≠ K}, tildeOf Zz ⁅uOfL22 T M, K''⁆) :=
      ⟨h1, h3⟩
    rw [hc23.2.2.2 K hK] at h4
    exact secMk_eq_one_iff.mp (Subgroup.mem_bot.mp h4)
  · exact le_inf le_sup_right le_sup_right

end Glue

@[expose] def Input14624NonFF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    Conc14619 T M → ∀ (K U₁ U₂ : Subgroup G) (s : G), K ∈ cComp (mcOf T) → KbarIsL3Two K →
      IsDecompUK T M K U₁ U₂ s →
      ∀ X : Subgroup G, X ≤ mcOf T → X ≤ Subgroup.normalizer (K : Set G) → IsElemAbelian 2 X →
        ¬ X ≤ centralizerMod (quasithinOmegaOneCenter T) X
          (⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T) →
          mIdx X (centralizerMod (quasithinOmegaOneCenter T) X
              (⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T)) + 1 ≤
            mIdx (⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T)
              (centralizerMod (quasithinOmegaOneCenter T)
                (⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T) X)

section ThreeC

theorem input14624ThreeC_of (hnff : Input14624NonFF) : Input14624ThreeC := by
  intro G _ _ T M S hB K U₁ U₂ s u γ γ' g hfull Kp hC hnorm
  classical
  by_contra hcon
  simp only [Claim24, not_or] at hcon
  obtain ⟨hnK, hnp⟩ := hcon
  obtain ⟨hctx, hall, hgeom⟩ := hfull
  obtain ⟨c19, -, c23, hKc, -, -, hdec, -⟩ := hctx
  obtain ⟨hsetup, hDlt, hpos, hle, hlt, -⟩ := hgeom
  obtain ⟨hNorm₁, hNorm₂, -⟩ := hnorm
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  obtain ⟨⟨U₁', U₂', s', hdecKp⟩, -⟩ := (hall Kp hC.mem).2
  have hXH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hsetup
  have hXab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hG
  have hXN : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun e he => by
    rw [S.normalizer_Z]; exact hXH he
  have hUKU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hKc)
  have hUpU := commutator_sup_le_U (T := T) (M := M) (le_of_mem_cComp hC.mem)
  refine ThreeC.claim_contra (Z := quasithinOmegaOneCenter T) (U := uOfL22 T M)
    (UK := ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T)
    (Up := ⁅uOfL22 T M, Kp⁆ ⊔ quasithinOmegaOneCenter T)
    (X := F8.Uγ (VZ T M) (mcOf T) (g : G)) (C := cuOf T M)
    (A₁ := F8.A₁ (quasithinOmegaOneCenter T) (g : G))
    (D := F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G))
    (Dg := F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G))
    hUab hXab hUN hUKU hUpU le_sup_right le_sup_right
    (inf_eq_Z_two S c23 hKc hC.mem hC.ne) (cuOf_le T M)
    (fun v hv => exists_decomp_two S c23 hC.comps hKc hC.mem hv)
    (fun c hc e he => (mem_cuOf.mp hc).2.2 e (hXH he)) hXN
    (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_commutator_sup (hNorm₁ he) (le_normalizer_conjClosure _ _ (hXH he)) (hXN he)) y).mp hy)
    (fun e he y hy => (Subgroup.mem_normalizer_iff.mp
      (mem_normalizer_commutator_sup (hNorm₂ he) (le_normalizer_conjClosure _ _ (hXH he)) (hXN he)) y).mp hy)
    (fun e he y hy => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ (hXH he)) y).mp hy)
    hF98.A₁_le_Uγ hF98.card_A₁ rfl hnK hnp (centralizerMod_le_left _ _ _)
    (fun x hx v hv => hx.2.2 v hv) (fun x hx h => ⟨hx, hXN hx, h⟩) hle hlt
    (fun hn => hnff G T M S hB c19 K U₁ U₂ s hKc hC.l3.1 hdec _ hXH hNorm₁ hXab hn)
    (fun hn => hnff G T M S hB c19 Kp U₁' U₂' s' hC.mem hC.l3.2 hdecKp _ hXH hNorm₂ hXab hn)

end ThreeC


end CFSG.Quasithin
