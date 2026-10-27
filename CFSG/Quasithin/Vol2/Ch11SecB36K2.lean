module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEPerm
public import CFSG.Quasithin.Vol2.Ch10SecD31B
public import CFSG.Quasithin.Vol2.Ch11SecABasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_centralizer_of_isTwoReducedIn {H K V : Subgroup G}
    (hR : IsTwoReducedIn H V) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hR.2.2.2 _ ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH) (fun x hx => ?_)
    fun d hd => ?_
  · have hKx : conjSubgroup K x = K :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (hHK hx)
    have := QuasithinUnique.C5.conjSubgroup_pCoreOf 2 K x
    rw [hKx] at this
    exact conjSubgroup_eq_iff_mem_normalizer.mp this
  · obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact Subgroup.one_mem _

theorem inf_centralizer_eq_pCoreOf {H K V : Subgroup G} (hR : IsTwoReducedIn H V) (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F] [Finite F] {k : ℕ}
    (hk : 2 ≤ k) (hF : Nat.card F = 2 ^ k)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hKC : ¬ K ≤ Subgroup.centralizer (V : Set G)) :
    K ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 K := by
  have hO := pCoreOf_le_centralizer_of_isTwoReducedIn hR hKH hHK
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) hO)
  have : Fintype F := Fintype.ofFinite F
  have hsimp : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    QuasithinUnique.AppE.sl2_isSimpleGroup hk (by rw [← Nat.card_eq_fintype_card, hF])
  have : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := e.isSimpleGroup
  set C := K ⊓ Subgroup.centralizer (V : Set G) with hCdef
  have hCK : C ≤ K := inf_le_left
  have hCn : (C.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCK).mpr
      (B2F.le_normalizer_inf Subgroup.le_normalizer
        (B2F.le_normalizer_centralizer (hKH.trans hR.2.1)))
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hNn : ((C.subgroupOf K).map π).Normal := hCn.map π (QuotientGroup.mk'_surjective _)
  have hO' : ∀ x (hx : x ∈ K), (⟨x, hx⟩ : ↥K) ∈ CFSG.pCore 2 ↥K → x ∈ pCoreOf 2 K := by
    intro x hx hxp
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    exact hxp
  rcases Subgroup.Normal.eq_bot_or_eq_top ((C.subgroupOf K).map π) with hbot | htop
  · intro x hx
    have hx1 : π ⟨x, hx.1⟩ = 1 := by
      have : π ⟨x, hx.1⟩ ∈ (C.subgroupOf K).map π :=
        ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact hO' x hx.1 hx1
  · exfalso
    apply hKC
    intro x hx
    have hmem : π ⟨x, hx⟩ ∈ (C.subgroupOf K).map π := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := hmem
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hcx
    have h1 : (c : G)⁻¹ * x ∈ pCoreOf 2 K := hO' _ (K.mul_mem (K.inv_mem c.2) hx) hcx
    have e1 : x = (c : G) * ((c : G)⁻¹ * x) := by group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.mp hc).2 (hO h1)

theorem autI_equiv_SL2 {H K V : Subgroup G} (hV : IsElemAbelian 2 V) (hR : IsTwoReducedIn H V)
    (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) {F : Type} [Field F] [Finite F]
    {k : ℕ} (hk : 2 ≤ k) (hF : Nat.card F = 2 ^ k)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hKC : ¬ K ≤ Subgroup.centralizer (V : Set G)) :
    Nonempty (↥(autI hV K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨e₁⟩ := Ch10.SecD.nonempty_autI_equiv hV (hKH.trans hR.2.1)
    (inf_centralizer_eq_pCoreOf hR hKH hHK hk hF e hKC)
  exact ⟨e₁.trans e⟩

omit [Finite G] in
theorem autI_le_normalizer_autI {V A K : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    autI hV A ≤ Subgroup.normalizer (autI hV K : Set (MulAut (IntMod V hV))) := by
  refine le_trans ?_ (Subgroup.le_normalizer_map (convI hV))
  refine Subgroup.map_mono fun a ha => ?_
  rw [Subgroup.mem_subgroupOf] at ha
  rw [Subgroup.mem_normalizer_iff]
  intro k
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using Subgroup.mem_normalizer_iff.mp (hAK ha) k

omit [Finite G] in
theorem iSup_map_fixV_eq_top {V K B Z : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVZ : V = conjClosure Z K) (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (hBN : B ≤ Subgroup.normalizer (V : Set G)) (hBZ : B ≤ Subgroup.centralizer (Z : Set G)) :
    (⨆ x ∈ autI hV K, (fixV (autI hV B)).map (x : MulAut (IntMod V hV)).toMonoidHom) = ⊤ := by
  set J := ⨆ x ∈ autI hV K, (fixV (autI hV B)).map (x : MulAut (IntMod V hV)).toMonoidHom
    with hJ
  let φ : IntMod V hV →* G :=
    { toFun := IntMod.val, map_one' := IntMod.val_one, map_mul' := IntMod.val_mul }
  have hZV : Z ≤ V := hVZ ▸ le_conjClosure Z K
  have key : V ≤ J.map φ := by
    refine hVZ.le.trans (conjClosure_le fun h hh z hz => ?_)
    let w : IntMod V hV := IntMod.mk hV ⟨z, hZV hz⟩
    have hw : w ∈ fixV (autI hV B) := (mem_fixV_autI hV hBN w).mpr
      (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (hBZ hy) z hz).symm)
    refine ⟨convI hV ⟨h, hKN hh⟩ w, ?_, convI_apply_val hV _ _⟩
    exact (le_iSup₂ (f := fun (x : MulAut (IntMod V hV)) (_ : x ∈ autI hV K) =>
      (fixV (autI hV B)).map (x : MulAut (IntMod V hV)).toMonoidHom)
      (convI hV ⟨h, hKN hh⟩) (convI_mem_autI hV hh (hKN hh))) ⟨w, hw, rfl⟩
  rw [eq_top_iff]
  intro w _
  obtain ⟨j, hj, hjw⟩ := key w.val_mem
  have : j = w := IntMod.val_injective hjw
  exact this ▸ hj

end CFSG.Quasithin.Vol2.Ch11.SecB
