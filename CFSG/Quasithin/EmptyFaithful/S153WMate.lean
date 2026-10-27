module

public import CFSG.Quasithin.EmptyFaithful.S153WCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Mate

public section

namespace CFSG.QuasithinUnique.AppCS2W

open CFSG.QuasithinUnique.AppCS2 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

structure WCfg2 (H S L : Subgroup G) (t : G) where
  D : WDbl H S L t
  P : A5Pi L
  hJ : P.im (thompsonJ S) = Estd
  hS : P.im (s2SI S L) = Dstd
  hX : P.im (L ⊔ thompsonJ S) = ⊤

theorem WDbl.nonempty_cfg {t : G} (D : WDbl H S L t) : Nonempty (WCfg2 H S L t) := by
  obtain ⟨⟨P, h1, h2, h3⟩⟩ := D.nonempty_std
  exact ⟨⟨D, P, h1, h2, h3⟩⟩

theorem WDbl.im_baum_eq {t : G} (D : WDbl H S L t) (P : A5Pi L) :
    P.im (baum S) = P.im (thompsonJ S) := by
  obtain ⟨τ₁, τ₂, -, -, -, hJeq, hBeq, -⟩ := D.core_B P
  exact hBeq.trans hJeq.symm

namespace WCfg2

variable {t : G} (C : WCfg2 H S L t)
include C

theorem hB : C.P.im (baum S) = Estd := (C.D.im_baum_eq C.P).trans C.hJ

theorem hBN : baum S ≤ normalizer (L : Set G) := C.D.hBN

theorem U_le_baum : blockU L ≤ baum S := C.D.blockU_le_baum C.P.toPiData

theorem V_le_baum {y : G} (hy : y ∈ normalizer (S : Set G)) : conjR (blockU L) y ≤ baum S := by
  have h1 := C5.conjSubgroup_mono C.U_le_baum y
  rwa [C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum S hy)] at h1

theorem V_le_N {y : G} (hy : y ∈ normalizer (S : Set G)) :
    conjR (blockU L) y ≤ normalizer (L : Set G) := (C.V_le_baum hy).trans C.hBN

theorem card_V (y : G) : Nat.card ↥(conjR (blockU L) y) = 16 := by
  rw [C56.conjR_eq, C5.card_conjSubgroup]
  exact C.P.card_blockU

theorem V_elem (y : G) : IsElemAbelian 2 (conjR (blockU L) y) :=
  C5.isElemAbelian_two_iff.mpr ((C5.isElemAbelian_two_iff.mp (isElemAbelian_blockU C.D.hL)).conjSubgroup y)

theorem key_count {y : G} (hy : y ∈ normalizer (S : Set G)) :
    Nat.card (C.P.im (conjR (blockU L) y)) *
      Nat.card (FixΔ (C.P.im (conjR (blockU L) y⁻¹))) = 16 := by
  have hVN := C.V_le_N hy
  have hV'N := C.V_le_N (inv_mem hy)
  have h4 := C.P.card_im_mul hVN
  have h5 := C.P.card_fix hV'N
  have hU : conjSubgroup (conjR (blockU L) y) y⁻¹ = blockU L :=
    C5.conjSubgroup_conjSubgroup_inv (blockU L) y
  have e : Nat.card ↥(conjR (blockU L) y ⊓ centralizer (blockU L : Set G)) =
      Nat.card ↥(blockU L ⊓ centralizer (conjR (blockU L) y⁻¹ : Set G)) := by
    rw [← C5.card_conjSubgroup (conjR (blockU L) y ⊓ centralizer (blockU L : Set G)) y⁻¹,
      C5.conjSubgroup_inf, C5.conjSubgroup_centralizer, hU]
    rfl
  rw [e, h5, C.card_V y] at h4
  exact h4

theorem im_V_le (y : G) (hy : y ∈ normalizer (S : Set G)) :
    C.P.im (conjR (blockU L) y) ≤ Estd := by
  rw [← C.hB]
  exact C.P.im_mono (C.V_le_baum hy)

theorem not_isTransv_of_not_mem {s : G} (hsS : s ∈ S) (hs : s ∉ normalizer (L : Set G)) :
    ¬ IsTransv S s := by
  rintro ⟨c, hc⟩
  have hD := C.D
  set F₁ : Subgroup G := blockU L ⊓ centralizer (thompsonJ S : Set G) with hF₁
  have hcardF : Nat.card ↥F₁ = 4 := by
    rw [hF₁, C.P.card_fix C.D.thompsonJ_le_N, C.hJ, card_fix_Estd]
  have hs' : s⁻¹ ∈ S := S.inv_mem hsS
  have hs'N : s⁻¹ ∉ normalizer (L : Set G) := fun h => hs (by simpa using inv_mem h)
  have hconj : conjR L s⁻¹ = conjR L t := C.D.conjR_eq_t_of_not_mem hs' hs'N
  have hU₂ : ∀ f ∈ blockU L, s * f * s⁻¹ ∈ blockU2 L t := by
    intro f hf
    have h1 : s * f * s⁻¹ ∈ conjR (blockU L) s⁻¹ := by
      show s * f * s⁻¹ ∈ conjSubgroup (blockU L) s⁻¹
      rw [mem_conjSubgroup_iff]
      have e : s⁻¹ * (s * f * s⁻¹) * s⁻¹⁻¹ = f := by group
      rw [e]
      exact hf
    rw [← blockU_conjR, hconj] at h1
    rw [blockU2_eq L t]
    exact h1
  let ψ : ↥F₁ → ↥({1, c} : Set G) := fun f =>
    ⟨(f : G)⁻¹ * (s * f * s⁻¹), by
      have := hc f (C.D.F1_le_Z0 f.2)
      rcases this with h | h
      · left; exact h
      · right; exact h⟩
  have hinj : Function.Injective ψ := by
    intro f f' h
    have h1 : (f : G)⁻¹ * (s * f * s⁻¹) = (f' : G)⁻¹ * (s * f' * s⁻¹) := congrArg Subtype.val h
    obtain ⟨h2, -⟩ := C.D.mul_unique ((blockU L).inv_mem f.2.1) ((blockU L).inv_mem f'.2.1)
      (hU₂ f f.2.1) (hU₂ f' f'.2.1) h1
    exact Subtype.ext (inv_injective h2)
  have hle := Nat.card_le_card_of_injective ψ hinj
  have h2 : Nat.card ↥({1, c} : Set G) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    calc ({1, c} : Set G).ncard ≤ ({c} : Set G).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  omega


end WCfg2

namespace WCfg2

variable {t : G} (C : WCfg2 H S L t)
include C

theorem exists_swapper : ∃ s₀ : G, s₀ ∈ S ∧ s₀ ∈ L ∧ C.P.pf s₀ ∈ Dset ∧ C.P.pf s₀ ∉ Eset := by
  classical
  have hSyl : IsSylowTwoOf (S ⊓ L) L := C.D.hcs.isSylowTwoOf_inf
  have hK₀2 : IsPGroup 2 ((S ⊓ L).subgroupOf L) :=
    hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  let Pp : Sylow 2 ↥L := hK₀2.toSylow hSyl.2.2
  have hcard := sylow_card_alt_five (Pp.mapSurjective C.P.hα)
  have hcoe : ((Pp.mapSurjective C.P.hα : Sylow 2 (alternatingGroup (Fin 5))) :
      Subgroup (alternatingGroup (Fin 5))) = ((S ⊓ L).subgroupOf L).map C.P.α := by
    rw [Sylow.coe_mapSurjective]
    rfl
  set K : Subgroup (Perm (Fin 5)) :=
    (((S ⊓ L).subgroupOf L).map C.P.α).map (alternatingGroup (Fin 5)).subtype with hKdef
  have hKcard : Nat.card K = 4 := by
    rw [hKdef, Subgroup.card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective,
      ← hcoe]
    exact hcard
  have hev : ∀ g ∈ K, Perm.sign g = 1 := by
    intro g hg
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.1 hg
    exact Equiv.Perm.mem_alternatingGroup.1 a.2
  obtain ⟨g, hgK, hgE⟩ := exists_not_mem_Eset K hev (by omega)
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hgK
  obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.1 ha
  have hℓ' : (ℓ : G) ∈ S ⊓ L := Subgroup.mem_subgroupOf.1 hℓ
  have hℓN : (ℓ : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer ℓ.2
  have hpf : C.P.pf (ℓ : G) = ((C.P.α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
    rw [C.P.pf_eq hℓN]
    exact C.P.hπα (ℓ : G) ℓ.2
  have hS₁ : (ℓ : G) ∈ s2SI S L := ⟨hℓ'.1, hℓN⟩
  have hD : C.P.pf (ℓ : G) ∈ Dstd := by
    rw [← C.hS, C.P.mem_im_pf s2SI_le_normalizer]
    exact ⟨ℓ, hS₁, rfl⟩
  refine ⟨ℓ, hℓ'.1, hℓ'.2, (mem_Dstd _).1 hD, ?_⟩
  rw [hpf]
  exact hgE

theorem bf_fix_E {u : G} (hu : u ∈ blockU L ⊓ centralizer (thompsonJ S : Set G)) :
    ∀ σ ∈ Eset, pact σ (C.P.bf u).1 = (C.P.bf u).1 := by
  intro σ hσ
  have hσE : σ ∈ C.P.im (thompsonJ S) := by rw [C.hJ]; exact (mem_Estd σ).2 hσ
  obtain ⟨y, hy, rfl⟩ := (C.P.mem_im_pf C.D.thompsonJ_le_N).1 hσE
  have hc : y * u = u * y := Subgroup.mem_centralizer_iff.1 hu.2 y hy
  have := (C.P.comm_iff (C.D.thompsonJ_le_N hy) hu.1).1 hc
  exact congrArg Subtype.val this

theorem exists_transv : ∃ s₀ : G, s₀ ∈ S ∧ s₀ ∈ L ∧ C.P.pf s₀ ∈ Dset ∧ C.P.pf s₀ ∉ Eset ∧
    IsTransv S s₀ := by
  classical
  obtain ⟨s₀, hs₀S, hs₀L, hD, hE⟩ := C.exists_swapper
  refine ⟨s₀, hs₀S, hs₀L, hD, hE, ?_⟩
  have hL := C.D.hL
  have hs₀N : s₀ ∈ normalizer (L : Set G) := Subgroup.le_normalizer hs₀L
  have hz0 : isEven z0 := by decide +kernel
  obtain ⟨cstar, hcstarU, hcstar⟩ := C.P.bf_surj ⟨z0, (mem_evenWeight_iff _).2 hz0⟩
  refine ⟨cstar, fun z hz => ?_⟩
  obtain ⟨u, huF, hcent, hdZ⟩ := C.D.Z0_decomp C.P hz
  have hu : u ∈ blockU L := huF.1
  have hd_s : s₀ * (u * z) = (u * z) * s₀ := hcent s₀ hs₀L
  set c : G := u * (s₀ * u⁻¹ * s₀⁻¹) with hc
  have hcU : c ∈ blockU L := by
    have h1 : s₀ * u⁻¹ * s₀⁻¹ ∈ blockU L := PiData.conj_mem_U hs₀N ((blockU L).inv_mem hu)
    exact (blockU L).mul_mem hu h1
  have hcL : c ∈ L := C.D.blockU_le_L hcU
  have hdc : c * (u * z) = (u * z) * c := hcent c hcL
  have hval : z⁻¹ * (s₀ * z * s₀⁻¹) = c := by
    have hz : z = u⁻¹ * (u * z) := by group
    have e1 : z⁻¹ * (s₀ * z * s₀⁻¹) = (u * z)⁻¹ * c * (u * z) := by
      have : s₀ * z * s₀⁻¹ = (s₀ * u⁻¹ * s₀⁻¹) * ((u * z) * s₀ * s₀⁻¹) := by
        calc s₀ * z * s₀⁻¹ = s₀ * (u⁻¹ * (u * z)) * s₀⁻¹ := by rw [← hz]
          _ = (s₀ * u⁻¹ * s₀⁻¹) * (s₀ * (u * z) * s₀⁻¹) := by group
          _ = (s₀ * u⁻¹ * s₀⁻¹) * (((u * z) * s₀) * s₀⁻¹) := by rw [hd_s]
      calc z⁻¹ * (s₀ * z * s₀⁻¹) = ((u * z)⁻¹ * u) * ((s₀ * u⁻¹ * s₀⁻¹) * ((u * z) * s₀ * s₀⁻¹)) := by
            rw [← this]; group
        _ = (u * z)⁻¹ * c * (u * z) := by rw [hc]; group
    rw [e1]
    calc (u * z)⁻¹ * c * (u * z) = (u * z)⁻¹ * ((u * z) * c) := by rw [← hdc]; group
      _ = c := by group
  rw [hval]
  have hwfix := C.bf_fix_E huF
  have hbf_inv : C.P.bf u⁻¹ = C.P.bf u := by
    have hsq : u⁻¹ = u := by
      have := C1.blockU_sq hL u hu
      exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using this)
    rw [hsq]
  have hbfc : C.P.bf c = C.P.bf u + vact (C.P.pf s₀) (C.P.bf u) := by
    rw [hc, C.P.bf_mul hu (PiData.conj_mem_U hs₀N ((blockU L).inv_mem hu)),
      C.P.bf_conj hs₀N ((blockU L).inv_mem hu), hbf_inv]
  have hwe : isEven (C.P.bf u).1 := (mem_evenWeight_iff _).1 (C.P.bf u).2
  rcases phi_two (C.P.pf s₀) hD hE (C.P.bf u).1 hwe hwfix with h | h
  · left
    have : C.P.bf c = C.P.bf 1 := by
      rw [C.P.bf_one, hbfc]
      apply Subtype.ext
      simpa [vact, add_comm] using h
    exact C.P.bf_inj hcU (one_mem _) this
  · right
    have : C.P.bf c = C.P.bf cstar := by
      rw [hcstar, hbfc]
      apply Subtype.ext
      simpa [vact, add_comm] using h
    exact C.P.bf_inj hcU hcstarU this

theorem im_V_eq {x : G} (hx : x ∈ normalizer (S : Set G))
    (hUV : ⁅blockU L, conjR (blockU L) x⁆ ≠ ⊥) : C.P.im (conjR (blockU L) x) = Estd := by
  classical
  set V := conjR (blockU L) x with hV
  have hVN := C.V_le_N hx
  have hV'N := C.V_le_N (inv_mem hx)
  have hWne : C.P.im V ≠ ⊥ := by
    intro hbot
    apply hUV
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvN : v ∈ normalizer (L : Set G) := hVN hv
    have h1 : C.P.π ⟨v, hvN⟩ = 1 := by
      have : C.P.π ⟨v, hvN⟩ ∈ C.P.im V := C.P.pi_mem_im hv
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    have h2 := (C.P.hker ⟨v, hvN⟩).1 h1 u hu
    calc v * u = (v * u * v⁻¹) * v := by group
      _ = u * v := by rw [h2]
  have hel := C.P.im_elemAbelian (C.V_elem x)
  have hel' := C.P.im_elemAbelian (C.V_elem x⁻¹)
  obtain ⟨a, haW, b, hbW, hW4, hWcard, hWfix⟩ := exists_four_card (C.P.im V) hel.1 hel.2
  obtain ⟨a', ha'W, b', hb'W, hW'4, hW'card, hW'fix⟩ :=
    exists_four_card (C.P.im (conjR (blockU L) x⁻¹)) hel'.1 hel'.2
  have hEset : ∀ g ∈ C.P.im V, g ∈ Eset := fun g hg => (mem_Estd g).1 (C.im_V_le x hx hg)
  have hE' : ∀ g ∈ C.P.im (conjR (blockU L) x⁻¹), g ∈ Eset := fun g hg =>
    (mem_Estd g).1 (C.im_V_le x⁻¹ (inv_mem hx) hg)
  have hc1 := C.key_count hx
  have hc2 := C.key_count (inv_mem hx)
  rw [inv_inv] at hc2
  have hW'fixc : Nat.card (FixΔ (C.P.im (conjR (blockU L) x⁻¹))) = (fixOf a' b').card := hW'fix
  obtain ⟨s₀, hs₀S, hs₀L, hD, hE, hTr⟩ := C.exists_transv
  have hy₀S : x * s₀ * x⁻¹ ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1 hx s₀).1 hs₀S
    exact this
  have hy₀N : x * s₀ * x⁻¹ ∈ normalizer (L : Set G) := by
    by_contra hcon
    exact C.not_isTransv_of_not_mem hy₀S hcon (hTr.conj hx)
  have hs₀N : s₀ ∈ normalizer (L : Set G) := Subgroup.le_normalizer hs₀L
  have hy₀U : conjR (blockU L) (x * s₀ * x⁻¹) = blockU L :=
    C5.conjSubgroup_eq_self (C1.mem_normalizer_blockU hy₀N)
  have hs₀V : conjR V s₀ = V := by
    rw [hV, WDbl.conjR_conjR]
    have e : x * s₀ = (x * s₀ * x⁻¹) * x := by group
    rw [e, ← WDbl.conjR_conjR, hy₀U]
  have hVmem : ∀ v ∈ V, s₀ * v * s₀⁻¹ ∈ V := by
    intro v hv
    have : v ∈ conjSubgroup V s₀ := by
      show v ∈ conjR V s₀
      rw [hs₀V]; exact hv
    exact mem_conjSubgroup_iff.1 this
  have hdW : ∀ g ∈ C.P.im V, C.P.pf s₀ * g * (C.P.pf s₀)⁻¹ ∈ C.P.im V := by
    intro g hg
    obtain ⟨v, hv, rfl⟩ := (C.P.mem_im).1 hg
    have h1 : C.P.pf s₀ * C.P.π v * (C.P.pf s₀)⁻¹ = C.P.π ⟨s₀ * (v : G) * s₀⁻¹, mul_mem
        (mul_mem hs₀N v.2) (inv_mem hs₀N)⟩ := by
      rw [C.P.pf_eq hs₀N, ← map_inv C.P.π ⟨s₀, hs₀N⟩, ← map_mul C.P.π, ← map_mul C.P.π]
      rfl
    rw [h1]
    exact C.P.pi_mem_im (hVmem v hv)
  have hK := K_fin a ((hEset a haW)) b (hEset b hbW) a' (hE' a' ha'W) b' (hE' b' hb'W) (C.P.pf s₀)
    hD
  have hWfourEq : four a b = Eset := by
    apply hK hE
    · intro g hg
      have hg' : g ∈ C.P.im V := (hW4 g).2 hg
      exact (hW4 _).1 (hdW g hg')
    · intro h1
      apply hWne
      rw [eq_bot_iff]
      intro g hg
      have := (hW4 g).1 hg
      rw [h1] at this
      exact Subgroup.mem_bot.2 (Finset.mem_singleton.1 this)
    · rw [← hWcard, ← hW'fixc]
      exact hc1
    · rw [← hW'card, ← hWfix]
      exact hc2
  ext g
  rw [hW4 g, hWfourEq, mem_Estd]

end WCfg2

end CFSG.QuasithinUnique.AppCS2W
