module

public import CFSG.Quasithin.H13.A7NatAssembly
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317B

public section

namespace CFSG.Quasithin.H13.L3322

open Equiv Equiv.Perm
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique hiding evenWeight
open CFSG.Quasithin.H13.A7 (IsCoordAct vec)
open CFSG.Quasithin.SteinbergCB (permAct7 evenWeight sevenP vecStab permAct7_apply)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem natural (h8 : Stmt3_3_8) (h10 : Stmt3_3_10) (h14 : Stmt3_3_14) (h17 : Stmt3_3_17)
    (h : Hyp331 G T M L D) (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) :
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      AlternatingNatural (autOn L (vPlus L T)) (commVPlus L T L) ⊥ 7 := by
  obtain ⟨hab, hc⟩ := L3317.alt7_cases h8 h10 h14 h e
  refine ⟨hab, ?_⟩
  rcases hc with hn | hc4
  · exact hn
  · exfalso
    have h6 := h17 G T M L D h ⟨e⟩
    rw [h6] at hc4
    norm_num at hc4

theorem exists_coord (h : Hyp331 G T M L D) [IsMulCommutative ↥(vPlus L T)]
    (hnat : AlternatingNatural (autOn L (vPlus L T)) (commVPlus L T L) ⊥ 7) :
    ∃ ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7),
      (∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ) ∧
      ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ := by
  classical
  have hLV := L3317.le_normalizer_vPlus h
  have hWV := L3317.commV_le_vPlus h
  obtain ⟨π, hπs, -, -, hU, -, -, -, β, hβs, hβk, hβe⟩ := hnat
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, hβk, Subgroup.mem_bot] at hu
    exact Subgroup.mem_bot.2 (Subtype.ext hu)
  set Q7 := ↥(FFModel.altDn 7).sec ⧸ (FFModel.altDn 7).ker.subgroupOf (FFModel.altDn 7).sec
  let e1 : ↥⁅vPlus L T, L⁆ ≃* ↥(commVPlus L T L) := (Subgroup.subgroupOfEquivOfLe hWV).symm
  let e2 : ↥(commVPlus L T L) ≃* Q7 := MulEquiv.ofBijective β ⟨hβinj, hβs⟩
  let e3 : Q7 ≃* ↥(FFModel.altDn 7).sec :=
    (MulEquiv.ofBijective (QuotientGroup.mk' _)
      ⟨A7.altDn_seven_mk_injective, QuotientGroup.mk_surjective⟩).symm
  let ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7) :=
    e1.trans (e2.trans (e3.trans A7.coreModSevenEquiv))
  have hmk : ∀ u : ↥(commVPlus L T L), (QuotientGroup.mk (e3 (β u)) : Q7) = β u :=
    fun u => e3.symm_apply_apply (β u)
  have hvec : ∀ w : ↥⁅vPlus L T, L⁆, vec ψ w =
      Multiplicative.toAdd ((e3 (β (e1 w))).1 : G6.PermMod 7) := fun w => rfl
  have hequi : ∀ (γ : alternatingGroup (Fin 7)) (w : ↥⁅vPlus L T, L⁆)
      (hw : ((((π γ : autOn L (vPlus L T)) : MulAut ↥(vPlus L T)) ⟨w, hWV w.2⟩ : ↥(vPlus L T)) :
        G) ∈ ⁅vPlus L T, L⁆),
      vec ψ ⟨_, hw⟩ = permAct7 γ (vec ψ w) := by
    intro γ w hw
    set m := e3 (β (e1 w)) with hm
    have hm' : G6.permAct 7 (γ : Perm (Fin 7)) (m.1 : G6.PermMod 7) ∈ G6.coreMod 7 :=
      G6.permAct_mem_coreMod _ m.2
    have hu : ((π γ : autOn L (vPlus L T)) : MulAut ↥(vPlus L T)) ((e1 w : ↥(commVPlus L T L)) :
        ↥(vPlus L T)) ∈ commVPlus L T L := hw
    have h1 := hβe γ (e1 w) m hu hm' (hmk (e1 w)).symm
    have h2 : e3 (β ⟨((π γ : autOn L (vPlus L T)) : MulAut ↥(vPlus L T))
        ((e1 w : ↥(commVPlus L T L)) : ↥(vPlus L T)), hu⟩) =
        ⟨G6.permAct 7 (γ : Perm (Fin 7)) (m.1 : G6.PermMod 7), hm'⟩ := by
      rw [h1]
      exact e3.apply_symm_apply _
    have h3 : e1 ⟨_, hw⟩ = ⟨((π γ : autOn L (vPlus L T)) : MulAut ↥(vPlus L T))
        ((e1 w : ↥(commVPlus L T L)) : ↥(vPlus L T)), hu⟩ := rfl
    rw [hvec, h3, h2, hvec, ← hm]
    rfl
  have hconj : ∀ (l : G) (hl : l ∈ L), ∃ γ : alternatingGroup (Fin 7),
      ∀ x : ↥(vPlus L T), ((((π γ : autOn L (vPlus L T)) : MulAut ↥(vPlus L T)) x :
        ↥(vPlus L T)) : G) = l * x * l⁻¹ := by
    intro l hl
    have hmem : conjAct (vPlus L T) ⟨l, hLV hl⟩ ∈ autOn L (vPlus L T) :=
      Subgroup.mem_map_of_mem _ (show (⟨l, hLV hl⟩ : Subgroup.normalizer
        ((vPlus L T : Subgroup G) : Set G)) ∈ L.subgroupOf _ from hl)
    obtain ⟨γ, hγ⟩ := hπs ⟨_, hmem⟩
    refine ⟨γ, fun x => ?_⟩
    rw [hγ]
    rfl
  refine ⟨ψ, fun l hl => ?_, fun σ hσ => ?_⟩
  · obtain ⟨γ, hγ⟩ := hconj l hl
    refine ⟨γ, γ.2, fun x y hxy => ?_⟩
    have hw : ((((π γ : autOn L (vPlus L T)) : MulAut ↥(vPlus L T)) ⟨x, hWV x.2⟩ :
        ↥(vPlus L T)) : G) ∈ ⁅vPlus L T, L⁆ := by
      rw [hγ]
      exact (Subgroup.mem_normalizer_iff.1 (L3317.le_normalizer_commV h hl) x).1 x.2
    have : y = ⟨_, hw⟩ := Subtype.ext (by rw [hxy, hγ])
    rw [this, hequi]
  · obtain ⟨⟨a, ha⟩, ha'⟩ : ∃ a, a = π ⟨σ, hσ⟩ := ⟨_, rfl⟩
    obtain ⟨⟨l, hlN⟩, hlL, hla⟩ := Subgroup.mem_map.1 ha
    have hlL' : l ∈ L := hlL
    refine ⟨l, hlL', fun x y hxy => ?_⟩
    have h1 : ((π ⟨σ, hσ⟩ : autOn L (vPlus L T)) : MulAut ↥(vPlus L T)) =
        conjAct (vPlus L T) ⟨l, hlN⟩ := by
      rw [← ha']
      exact hla.symm
    have hw : ((((π ⟨σ, hσ⟩ : autOn L (vPlus L T)) : MulAut ↥(vPlus L T)) ⟨x, hWV x.2⟩ :
        ↥(vPlus L T)) : G) ∈ ⁅vPlus L T, L⁆ := by
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.1 (L3317.le_normalizer_commV h hlL') x).1 x.2
    have hval : ((((π ⟨σ, hσ⟩ : autOn L (vPlus L T)) : MulAut ↥(vPlus L T)) ⟨x, hWV x.2⟩ :
        ↥(vPlus L T)) : G) = l * x * l⁻¹ := by
      rw [h1]
      rfl
    have : y = ⟨_, hw⟩ := Subtype.ext (by rw [hxy]; exact hval.symm)
    rw [this, hequi]


theorem le_M (h5 : Stmt3_3_5) (h : Hyp331 G T M L D) (hML : mPlus L T = L) {X : Subgroup G}
    (hX : L ⊔ T ≤ X) (hO : pCoreOf 2 X ≠ ⊥) : X ≤ M := by
  obtain ⟨-, hU, -⟩ := h5 G T M L h.toSetup331
  rw [hML] at hU
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have := hU.2 M' ⟨hM'.1, hX.trans hM'.2⟩
  exact this ▸ hM'.2

theorem normalizer_commV_le (h5 : Stmt3_3_5) (h14 : Stmt3_3_14) (h : Hyp331 G T M L D)
    (hML : mPlus L T = L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)) :
    Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (le_M h5 h hML (sup_le (L3317.le_normalizer_commV h) (L3317.T_le_normalizer_commV hTL))
    ?_).trans (h14 G T M L D h).2
  have hp : IsPGroup 2 ↥⁅vPlus L T, L⁆ := isPGroup_two_of_sq_eq_one fun w => by
    rw [sq]
    exact A7.sq_eq_one_of_vec ψ w
  have hle : ⁅vPlus L T, L⁆ ≤ pCoreOf 2 (Subgroup.normalizer
      ((⁅vPlus L T, L⁆ : Subgroup G) : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hp
  intro hb
  rw [hb, le_bot_iff] at hle
  have h64 := A7.nat_card_of_vec ψ
  rw [hle, Subgroup.card_bot] at h64
  norm_num at h64

theorem exists_relabel_aligned {T L W : Subgroup G} (hT : quasithinIsSylowTwo T)
    (ψ : W ≃* Multiplicative (evenWeight 7)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ)
    (hNact : ∀ n ∈ Subgroup.normalizer (W : Set G), ∃ σ, IsCoordAct ψ n σ) :
    ∃ τ : Perm (Fin 7), ∀ σ : Perm (Fin 7),
      (∃ t ∈ T, IsCoordAct (ψ.trans (A7.relabelE τ)) t σ) ↔
        σ ∈ sevenP ∧ ∃ n ∈ Subgroup.normalizer (W : Set G),
          IsCoordAct (ψ.trans (A7.relabelE τ)) n σ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (W : Set G) with hNdef
  set ρ := A7.coordRep ψ (le_refl N) hNact with hρ
  set B := ρ.range with hBdef
  have hρspec : ∀ n : N, IsCoordAct ψ n (ρ n) := A7.coordRep_spec ψ (le_refl N) hNact
  have hρeq : ∀ (n : N) {σ : Perm (Fin 7)}, IsCoordAct ψ n σ → ρ n = σ := fun n σ hσ =>
    A7.IsCoordAct.unique ψ n.2 (hρspec n) hσ
  have hAB : alternatingGroup (Fin 7) ≤ B := by
    intro σ hσ
    obtain ⟨l, hl, hact⟩ := hLonto σ hσ
    exact ⟨⟨l, hLW hl⟩, hρeq _ hact⟩
  have hB := A7.eq_alternating_or_eq_top hAB
  set TG : Sylow 2 G := hT.1.toSylow hT.2 with hTG
  have hTGcoe : (TG : Subgroup G) = T := IsPGroup.toSylow_coe hT.1 hT.2
  have hTN : (TG : Subgroup G) ≤ N := hTGcoe ▸ hTW
  set TN : Sylow 2 N := TG.subtype hTN with hTNdef
  set TB : Sylow 2 B := TN.mapSurjective ρ.rangeRestrict_surjective with hTBdef
  obtain ⟨hS2, hSidx⟩ := A7.sevenP_inf_isSylow hB
  set S0 : Sylow 2 B := hS2.toSylow hSidx with hS0def
  have hS0coe : (S0 : Subgroup B) = (sevenP ⊓ B).subgroupOf B := IsPGroup.toSylow_coe hS2 hSidx
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B S0 TB
  have hTBmem : ∀ σ : B, σ ∈ (TB : Subgroup B) ↔ ∃ t ∈ T, ∃ ht : t ∈ N, ρ ⟨t, ht⟩ = σ := by
    intro σ
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : ((t : G)) ∈ T := by
        have : t ∈ (TG : Subgroup G).subgroupOf N := ht
        rw [Subgroup.mem_subgroupOf, hTGcoe] at this
        exact this
      exact ⟨t, ht', t.2, rfl⟩
    · rintro ⟨t, ht, htN, hσ⟩
      refine ⟨⟨t, htN⟩, ?_, Subtype.ext hσ⟩
      show (⟨t, htN⟩ : N) ∈ (TG : Subgroup G).subgroupOf N
      rw [Subgroup.mem_subgroupOf, hTGcoe]
      exact ht
  have hbmem : ∀ σ : B, σ ∈ (TB : Subgroup B) ↔ b⁻¹ * σ * b ∈ (S0 : Subgroup B) := by
    intro σ
    rw [← hb, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  set τ : Perm (Fin 7) := (b : Perm (Fin 7))⁻¹ with hτ
  refine ⟨τ, fun σ => ?_⟩
  have hbB : (b : Perm (Fin 7)) ∈ B := b.2
  constructor
  · rintro ⟨t, ht, hact⟩
    rw [A7.isCoordAct_trans_relabelE_iff'] at hact
    have htN : t ∈ N := hTW ht
    set σ₀ := τ⁻¹ * σ * τ with hσ₀
    have hσ₀B : σ₀ ∈ B := ⟨⟨t, htN⟩, hρeq ⟨t, htN⟩ hact⟩
    have h1 : (⟨σ₀, hσ₀B⟩ : B) ∈ (TB : Subgroup B) :=
      (hTBmem _).2 ⟨t, ht, htN, hρeq ⟨t, htN⟩ hact⟩
    rw [hbmem, hS0coe, Subgroup.mem_subgroupOf] at h1
    have h2 : ((b⁻¹ * ⟨σ₀, hσ₀B⟩ * b : B) : Perm (Fin 7)) = σ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      show (b : Perm (Fin 7))⁻¹ * σ₀ * b = σ
      rw [hσ₀, hτ, inv_inv]
      group
    rw [h2] at h1
    exact ⟨(Subgroup.mem_inf.1 h1).1, t, htN, (A7.isCoordAct_trans_relabelE_iff' ψ τ).2 hact⟩
  · rintro ⟨hσP, n, hn, hact⟩
    rw [A7.isCoordAct_trans_relabelE_iff'] at hact
    set σ₀ := τ⁻¹ * σ * τ with hσ₀
    have hσ₀B : σ₀ ∈ B := ⟨⟨n, hn⟩, hρeq ⟨n, hn⟩ hact⟩
    have hσB : σ ∈ B := by
      have : σ = (b : Perm (Fin 7))⁻¹ * σ₀ * b := by
        rw [hσ₀, hτ, inv_inv]
        group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hbB) hσ₀B) hbB
    have h1 : (⟨σ₀, hσ₀B⟩ : B) ∈ (TB : Subgroup B) := by
      rw [hbmem, hS0coe, Subgroup.mem_subgroupOf]
      have h2 : ((b⁻¹ * ⟨σ₀, hσ₀B⟩ * b : B) : Perm (Fin 7)) = σ := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        show (b : Perm (Fin 7))⁻¹ * σ₀ * b = σ
        rw [hσ₀, hτ, inv_inv]
        group
      rw [h2]
      exact Subgroup.mem_inf.2 ⟨hσP, hσB⟩
    obtain ⟨t, ht, htN, htσ⟩ := (hTBmem _).1 h1
    refine ⟨t, ht, (A7.isCoordAct_trans_relabelE_iff' ψ τ).2 ?_⟩
    have := hρspec ⟨t, htN⟩
    rw [htσ] at this
    exact this


@[expose] def vecZO : Fin 7 → ZMod 2 := Pi.single 0 1 + Pi.single 1 1

@[expose] def vecTF : Fin 7 → ZMod 2 :=
  Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1

@[expose] def sP1 : Perm (Fin 7) := swap 0 1 * swap 2 3

@[expose] def sP2 : Perm (Fin 7) := swap 0 1 * swap 4 5

@[expose] def sP3 : Perm (Fin 7) := swap 2 4 * swap 3 5

theorem sP_mem : sP1 ∈ sevenP ⊓ alternatingGroup (Fin 7) ∧
    sP2 ∈ sevenP ⊓ alternatingGroup (Fin 7) ∧ sP3 ∈ sevenP ⊓ alternatingGroup (Fin 7) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · exact Equiv.Perm.mem_alternatingGroup.2 (by decide)
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · exact Equiv.Perm.mem_alternatingGroup.2 (by decide)
  · exact Subgroup.subset_closure (by simp [sP3])
  · exact Equiv.Perm.mem_alternatingGroup.2 (by decide)

theorem fixed_sP : ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 → permAct7 sP1 v = v →
    permAct7 sP2 v = v → permAct7 sP3 v = v →
    v = 0 ∨ v = vecZO ∨ v = vecTF ∨ v = A7.vecSix := by
  decide +kernel

theorem sevenP_fix_vecSix {g : Perm (Fin 7)} (hg : g ∈ sevenP) :
    permAct7 g A7.vecSix = A7.vecSix := by
  have hstab : sevenP ≤ vecStab A7.vecSix := by
    rw [sevenP, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    show permAct7 g A7.vecSix = A7.vecSix
    rcases hg with rfl | rfl | rfl | rfl <;> (funext i; fin_cases i <;> decide)
  exact hstab hg

theorem fixed_threeCycles : ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 →
    permAct7 (swap 0 2 * swap 0 1) v = v → permAct7 (swap 2 4 * swap 2 3) v = v →
    permAct7 (swap 4 6 * swap 4 5) v = v → v = 0 := by
  decide +kernel


structure Coord322 (T L : Subgroup G) (ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)) :
    Prop where
  Lact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ
  Lonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ
  Nact : ∀ n ∈ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G), ∃ σ, IsCoordAct ψ n σ
  Tact : ∀ t ∈ T, ∃ σ ∈ sevenP, IsCoordAct ψ t σ
  Tonto : ∀ σ ∈ sevenP ⊓ alternatingGroup (Fin 7), ∃ t ∈ T, IsCoordAct ψ t σ

theorem exists_coord322 (h5 : Stmt3_3_5) (h8 : Stmt3_3_8) (h10 : Stmt3_3_10)
    (h14 : Stmt3_3_14) (h17 : Stmt3_3_17) (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) :
    ∃ ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7), Coord322 T L ψ := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hab, hnat⟩ := natural h8 h10 h14 h17 h e
  obtain ⟨ψ, hLact, hLonto⟩ := exists_coord h hnat
  have hLW := L3317.le_normalizer_commV h
  have hTW := L3317.T_le_normalizer_commV hTL
  have hNact := A7.nact_of_lact hLW hLact hLonto (normalizer_commV_le h5 h14 h hML hTL ψ)
  obtain ⟨τ, hτ⟩ := exists_relabel_aligned h.sylow ψ hLW hTW hLonto hNact
  refine ⟨ψ.trans (A7.relabelE τ), ⟨fun l hl => ?_, fun σ hσ => ?_, fun n hn => ?_,
    fun t ht => ?_, fun σ hσ => ?_⟩⟩
  · obtain ⟨σ, hσ, hact⟩ := hLact l hl
    exact ⟨τ * σ * τ⁻¹, (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ,
      (A7.isCoordAct_trans_relabelE_iff ψ τ).2 hact⟩
  · have hσ' : τ⁻¹ * σ * τ⁻¹⁻¹ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ⁻¹
    rw [inv_inv] at hσ'
    obtain ⟨l, hl, hact⟩ := hLonto _ hσ'
    exact ⟨l, hl, (A7.isCoordAct_trans_relabelE_iff' ψ τ).2 hact⟩
  · obtain ⟨σ, hact⟩ := hNact n hn
    exact ⟨τ * σ * τ⁻¹, (A7.isCoordAct_trans_relabelE_iff ψ τ).2 hact⟩
  · obtain ⟨σ, hact⟩ := hNact t (hTW ht)
    have hact' := (A7.isCoordAct_trans_relabelE_iff ψ τ).2 hact
    exact ⟨_, ((hτ _).1 ⟨t, ht, hact'⟩).1, hact'⟩
  · have hσA := (Subgroup.mem_inf.1 hσ).2
    have hσ' : τ⁻¹ * σ * τ⁻¹⁻¹ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσA τ⁻¹
    rw [inv_inv] at hσ'
    obtain ⟨l, hl, hact⟩ := hLonto _ hσ'
    exact (hτ σ).2 ⟨(Subgroup.mem_inf.1 hσ).1, l, hLW hl,
      (A7.isCoordAct_trans_relabelE_iff' ψ τ).2 hact⟩

section Z

variable {ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)}

theorem mem_Z_iff (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hc : Coord322 T L ψ) (x : ↥⁅vPlus L T, L⁆) :
    (x : G) ∈ quasithinOmegaOneCenter T ↔
      vec ψ x = 0 ∨ vec ψ x = vecZO ∨ vec ψ x = vecTF ∨ vec ψ x = A7.vecSix := by
  have hTW := L3317.T_le_normalizer_commV hTL
  constructor
  · intro hx
    have hfix : ∀ σ ∈ sevenP ⊓ alternatingGroup (Fin 7), permAct7 σ (vec ψ x) = vec ψ x := by
      intro σ hσ
      obtain ⟨t, ht, hact⟩ := hc.Tonto σ hσ
      have hxt : t * (x : G) * t⁻¹ = x := by
        have := Subgroup.mem_centralizer_iff.1 (L246C127.le_centralizer_omegaOneCenter T ht) x hx
        rw [← this, mul_inv_cancel_right]
      have := hact x x hxt.symm
      exact this.symm
    obtain ⟨h1, h2, h3⟩ := sP_mem
    exact fixed_sP _ (SteinbergCB.mem_evenWeight.1 (A7.vec_mem ψ x)) (hfix _ h1) (hfix _ h2)
      (hfix _ h3)
  · intro hv
    refine A7.mem_omegaOneCenter_of_fixed (L3317.commV_le_T h) ψ hc.Tact hTW fun g hg => ?_
    rcases hv with hv | hv | hv | hv <;> rw [hv]
    · exact map_zero _
    · exact A7.sevenP_fix hg (Or.inl rfl)
    · exact A7.sevenP_fix hg (Or.inr rfl)
    · exact sevenP_fix_vecSix hg

omit [Finite G] in
theorem eq_one_of_centralizer (hc : Coord322 T L ψ) (x : ↥⁅vPlus L T, L⁆)
    (hx : ∀ l ∈ L, l * (x : G) = x * l) : x = 1 := by
  have hfix : ∀ σ ∈ alternatingGroup (Fin 7), permAct7 σ (vec ψ x) = vec ψ x := by
    intro σ hσ
    obtain ⟨l, hl, hact⟩ := hc.Lonto σ hσ
    have hxl : l * (x : G) * l⁻¹ = x := by rw [hx l hl, mul_inv_cancel_right]
    exact (hact x x hxl.symm).symm
  have h0 := fixed_threeCycles _ (SteinbergCB.mem_evenWeight.1 (A7.vec_mem ψ x))
    (hfix _ (Equiv.Perm.mem_alternatingGroup.2 (by decide)))
    (hfix _ (Equiv.Perm.mem_alternatingGroup.2 (by decide)))
    (hfix _ (Equiv.Perm.mem_alternatingGroup.2 (by decide)))
  exact (A7.vec_eq_zero_iff ψ x).1 h0

end Z


section Core

open Subgroup CFSG.Quasithin.H13.A7

theorem pCoreOf_autOn_eq_bot_six' {L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}
    (hLV : L ≤ normalizer (V : Set G))
    (hLact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ)
    (hLonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ)
    (hNact : ∀ n ∈ normalizer (V : Set G), ∃ σ, IsCoordAct ψ n σ) {e : V} (he : vec ψ e = vecSix)
    {X : Subgroup G} (hXV : X ≤ normalizer (V : Set G))
    (hXe : X ≤ centralizer ({(e : G)} : Set G))
    (hLeX : oTwoUpper (L ⊓ centralizer ({(e : G)} : Set G)) ≤ X) :
    pCoreOf 2 (autOn X V) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := autOn X V with hAdef
  have hA : ∀ a ∈ A, ∃ σ, IsCoordAut ψ a σ := by
    rintro a ⟨m, hm, rfl⟩
    obtain ⟨σ, hσ⟩ := hNact m m.2
    exact ⟨σ, isCoordAut_conjAct m.2 hσ⟩
  set ρ := coordAutHom A hA with hρ
  have hρi := coordAutHom_injective A hA
  have hfix : ∀ a : A, ρ a 6 = 6 := by
    rintro ⟨a, m, hm, rfl⟩
    have hspec := coordAutHom_spec A hA ⟨_, m, hm, rfl⟩
    have h1 := hspec e
    have h2 : (conjAct V m) e = e := by
      apply Subtype.ext
      show (m : G) * e * (m : G)⁻¹ = e
      have hme : (m : G) ∈ centralizer ({(e : G)} : Set G) := hXe hm
      rw [mem_centralizer_singleton_iff] at hme
      rw [hme, mul_inv_cancel_right]
    rw [h2, he] at h1
    exact (permAct7_vecSix_iff _).1 h1.symm
  have hstab : ∀ s ∈ stabA7 vecSix, ∃ a : A, ρ a = (s : Perm (Fin 7)) := by
    intro s hs
    rw [← natLam_map_Le_six hLV hLact hLonto he] at hs
    obtain ⟨l, hl, hls⟩ := hs
    rw [SetLike.mem_coe, mem_subgroupOf] at hl
    have hlX : (l : G) ∈ X := hLeX hl
    have hlN : (l : G) ∈ normalizer (V : Set G) := hXV hlX
    refine ⟨⟨conjAct V ⟨l, hlN⟩, ⟨l, hlN⟩, hlX, rfl⟩, ?_⟩
    apply IsCoordAut.unique (coordAutHom_spec A hA _)
    rw [← hls]
    exact isCoordAut_conjAct hlN (natLam_spec hLV hLact l)
  set P := pCoreOf 2 A with hPdef
  have hPA : P ≤ A := CFSG.LieType.BorelTits.pCoreOf_le 2 A
  have hPn : A ≤ normalizer (P : Set (MulAut ↥V)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A
  set Q := (P.subgroupOf A).map ρ with hQdef
  have hQ2 : IsPGroup 2 Q := (hP2.comap_of_injective _ A.subtype_injective).map ρ
  have hQn : ∀ (b : A) (q : Perm (Fin 7)), q ∈ Q → ρ b * q * (ρ b)⁻¹ ∈ Q := by
    rintro b _ ⟨x, hx, rfl⟩
    refine ⟨b * x * b⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.1 (hPn b.2) x).1 hx
  have hQeven : ∀ q ∈ Q, sign q = 1 → q = 1 := by
    intro q hq hqs
    have hs := isSimpleGroup_stabA7_vecSix
    set N₀ : Subgroup (stabA7 vecSix) :=
      { carrier := {s | ((s : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ Q}
        mul_mem' := fun ha hb => Q.mul_mem ha hb
        one_mem' := Q.one_mem
        inv_mem' := fun ha => Q.inv_mem ha } with hN₀
    have hN₀n : N₀.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨b, hb⟩ := hstab g g.2
      have := hQn b _ hn
      rw [hb] at this
      exact this
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hN₀n with h0 | h0
    · have hmem : (⟨⟨q, mem_alternatingGroup.2 hqs⟩, ?_⟩ : stabA7 vecSix) ∈ N₀ := hq
      · rw [h0, mem_bot] at hmem
        exact congrArg (fun s : stabA7 vecSix => ((s : alternatingGroup (Fin 7)) :
          Perm (Fin 7))) hmem
      · obtain ⟨x, -, rfl⟩ := hq
        exact (permAct7_vecSix_iff _).2 (hfix x)
    · exfalso
      have hc : (⟨⟨cycSix 0, mem_alternatingGroup.2 (cycSix_sign 0)⟩,
          (permAct7_vecSix_iff _).2 (cycSix_six 0)⟩ : stabA7 vecSix) ∈ N₀ := h0 ▸ mem_top _
      obtain ⟨n, hn⟩ := hQ2 ⟨cycSix 0, hc⟩
      have h3 : cycSix 0 ^ 3 = 1 := by decide
      have h1 : cycSix 0 ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have hord : orderOf (cycSix 0) ∣ Nat.gcd 3 (2 ^ n) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h1)
      rw [show Nat.gcd 3 (2 ^ n) = 1 from Nat.Coprime.pow_right _ (by norm_num), Nat.dvd_one,
        orderOf_eq_one_iff] at hord
      exact cycSix_ne_one hord
  have hQbot : ∀ q ∈ Q, q = 1 := by
    intro q hq
    obtain ⟨x, hx, hxq⟩ := hq
    have hq6 : q 6 = 6 := by rw [← hxq]; exact hfix x
    apply centralizer_stab_six q hq6
    intro i
    obtain ⟨c, hc⟩ := hstab ⟨cycSix i, mem_alternatingGroup.2 (cycSix_sign i)⟩
      ((permAct7_vecSix_iff _).2 (cycSix_six i))
    have h1 : ρ c * q * (ρ c)⁻¹ ∈ Q := hQn c q ⟨x, hx, hxq⟩
    have h2 : q⁻¹ * (ρ c * q * (ρ c)⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem ⟨x, hx, hxq⟩) h1
    have h3 := hQeven _ h2 (by simp [hc, cycSix_sign])
    rw [hc] at h3
    have h4 : cycSix i * q = q * cycSix i := by
      calc cycSix i * q = q * (q⁻¹ * (cycSix i * q * (cycSix i)⁻¹)) * cycSix i := by group
        _ = q * cycSix i := by rw [h3, mul_one]
    exact h4.symm
  rw [eq_bot_iff]
  intro a ha
  have h1 : ρ ⟨a, hPA ha⟩ = 1 :=
    hQbot _ ⟨⟨a, hPA ha⟩, by rwa [SetLike.mem_coe, mem_subgroupOf], rfl⟩
  have h2 : (⟨a, hPA ha⟩ : A) = 1 := hρi (by rw [h1, map_one])
  exact congrArg Subtype.val h2

end Core

section Theta

variable {ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)}

abbrev lTheta (L : Subgroup G) (e : G) : Subgroup G :=
  oTwoUpper (L ⊓ Subgroup.centralizer ({e} : Set G))

omit [Finite G] in
theorem lTheta_le (L : Subgroup G) (e : G) : lTheta L e ≤ L :=
  (oTwoUpper_le _).trans inf_le_left

omit [Finite G] in
theorem lTheta_le_centralizer (L : Subgroup G) (e : G) :
    lTheta L e ≤ Subgroup.centralizer ({e} : Set G) :=
  (oTwoUpper_le _).trans inf_le_right

theorem T_le_normalizer_lTheta (hTL : T ≤ Subgroup.normalizer (L : Set G)) {e : G}
    (he : e ∈ quasithinOmegaOneCenter T) :
    T ≤ Subgroup.normalizer (lTheta L e : Set G) := by
  intro t ht
  have h1 : t ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({e} : Set G) : Subgroup G) :
      Set G) := by
    refine CFSG.Quasithin.A4.mem_normalizer_inf (hTL ht) (Subgroup.le_normalizer ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (L246C127.le_centralizer_omegaOneCenter T ht) e he).symm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
  rw [← oTwoUpper_map, h1]

theorem pCoreOf_lTheta_sup (h7 : Stmt3_3_7) (h : Hyp331 G T M L D) (hML : mPlus L T = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hc : Coord322 T L ψ)
    {e : ↥⁅vPlus L T, L⁆} (he : vec ψ e = A7.vecSix)
    (heZ : (e : G) ∈ quasithinOmegaOneCenter T) :
    pCoreOf 2 (lTheta L (e : G) ⊔ T) = pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLW := L3317.le_normalizer_commV h
  have hTW := L3317.T_le_normalizer_commV hTL
  have hTe : T ≤ Subgroup.centralizer ({(e : G)} : Set G) := fun t ht => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (L246C127.le_centralizer_omegaOneCenter T ht) _ heZ).symm
  have hXW : lTheta L (e : G) ⊔ T ≤ Subgroup.normalizer
      ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) := sup_le ((lTheta_le L _).trans hLW) hTW
  have hXe : lTheta L (e : G) ⊔ T ≤ Subgroup.centralizer ({(e : G)} : Set G) :=
    sup_le (lTheta_le_centralizer L _) hTe
  have hO := pCoreOf_autOn_eq_bot_six' hLW hc.Lact hc.Lonto hc.Nact he hXW hXe le_sup_left
  have hPW := A7.pCoreOf_le_centralizer_of_autOn hXW rfl hO
  have hPT : pCoreOf 2 (lTheta L (e : G) ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
  refine le_antisymm ?_ ?_
  ·
    have h71 := (h7 G T M L D h).1.2
    rw [hML] at h71
    rw [← h71]
    refine le_inf hPT ?_
    have hdec := h.vPlus_decomp.2
    rw [hML] at hdec
    rw [Subgroup.le_centralizer_iff]
    refine (le_of_eq hdec).trans (sup_le ?_ ?_)
    · exact Subgroup.le_centralizer_iff.1 hPW
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact (Subgroup.mem_centralizer_iff.1 (L246C127.le_centralizer_omegaOneCenter T (hPT hp)) z
        (Subgroup.mem_inf.1 hz).1).symm
  ·
    have hQT : pCoreOf 2 (L ⊔ T) ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact (sup_le_sup_right (lTheta_le L _) T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

end Theta

end CFSG.Quasithin.H13.L3322
