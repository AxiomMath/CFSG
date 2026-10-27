module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenModBridge

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.Quasithin.F53Mod CFSG.Quasithin.F7 CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X P Z L N : Subgroup G}

theorem EvenMod.inf_sup_of_isCompl (D : Dict5 X P Z) (hsec : IsSec X L N)
    (hQ : ⁅N, pCoreOf 2 X⁆ ≤ L) {C F : Subgroup G} (hLC : L ≤ C) (hCN : C ≤ N) (hLF : L ≤ F)
    (hFN : F ≤ N) (h : IsCompl (secSub D hsec hQ C) (secSub D hsec hQ F)) :
    C ⊓ F = L ∧ C ⊔ F = N := by
  constructor
  · have h1 : secSub D hsec hQ (C ⊓ F) = ⊥ := by
      rw [secSub_inf D hsec hQ hLC hLF]
      exact h.inf_eq_bot
    exact le_antisymm ((secSub_eq_bot_iff D hsec hQ (inf_le_left.trans hCN)).mp h1)
      (le_inf hLC hLF)
  · have h1 : secSub D hsec hQ (C ⊔ F) = ⊤ := by
      rw [eq_top_iff, ← h.sup_eq_top]
      exact sup_le (secSub_mono D hsec hQ le_sup_left) (secSub_mono D hsec hQ le_sup_right)
    exact le_antisymm (sup_le hCN hFN)
      ((secSub_eq_top_iff D hsec hQ (hLC.trans le_sup_left)).mp h1)

theorem S18_sec (D : Dict5 X P Z) (hsec : IsSec X L N) (hQ : ⁅N, pCoreOf 2 X⁆ ≤ L)
    (hc : cSecIn X L N ≤ pCoreOf 2 X) {x : G} (hx : x ∈ X) (h2 : IsTransvec 1 x L N) :
    (D.ψ ⟨x, hx⟩).IsSwap ∧ fixSecIn X L N = fixSecIn (oTwoRes X) L N ∧
      ⁅N, X⁆ ⊔ L = ⁅N, oTwoRes X⁆ ⊔ L ∧
      fixSecIn X L N ⊓ (⁅N, X⁆ ⊔ L) = L ∧ fixSecIn X L N ⊔ (⁅N, X⁆ ⊔ L) = N ∧
      (fixSecIn X L N).relIndex N = 16 ∧ L.relIndex (⁅N, X⁆ ⊔ L) = 16 ∧
      L.relIndex N = L.relIndex (fixSecIn X L N) * 16 ∧ IsOrthSec X L (⁅N, X⁆ ⊔ L) := by
  set W := secMod D hsec hQ with hW
  have hf : W.Faithful := (secMod_faithful_iff D hsec hQ).mpr hc
  have ht : idx W (D.ψ ⟨x, hx⟩) = 2 := (isTransvec_one_iff D hsec hQ hx).mp h2
  obtain ⟨hsw, hCA, hFA, hcompl, hC16, hF16, ⟨eF⟩⟩ := S18_model W hf ht
  set C := fixSecIn X L N with hCdef
  set F := ⁅N, X⁆ ⊔ L with hFdef
  have hLC : L ≤ C := EvenMod.le_fixSecIn hsec le_rfl
  have hCN : C ≤ N := EvenMod.fixSecIn_le X L N
  have hLF : L ≤ F := le_sup_right
  have hFN : F ≤ N := EvenMod.commSec_le hsec le_rfl
  have hLCA : L ≤ fixSecIn (oTwoRes X) L N := EvenMod.le_fixSecIn hsec (oTwoRes_le X)
  have hLFA : L ≤ ⁅N, oTwoRes X⁆ ⊔ L := le_sup_right
  have hsC : secSub D hsec hQ C = fixW W ⊤ := secSub_fixSecIn_self D hsec hQ
  have hsF : secSub D hsec hQ F = commW W ⊤ ⊤ := secSub_commSec_self D hsec hQ
  have hCeq : C = fixSecIn (oTwoRes X) L N := by
    have h1 : secSub D hsec hQ C = secSub D hsec hQ (fixSecIn (oTwoRes X) L N) := by
      rw [hsC, secSub_fixSecIn_oTwoRes D hsec hQ, hCA]
    exact le_antisymm ((secSub_le_secSub_iff D hsec hQ hCN hLCA).mp h1.le)
      ((secSub_le_secSub_iff D hsec hQ (EvenMod.fixSecIn_le _ L N) hLC).mp h1.ge)
  have hFeq : F = ⁅N, oTwoRes X⁆ ⊔ L := by
    have h1 : secSub D hsec hQ F = secSub D hsec hQ (⁅N, oTwoRes X⁆ ⊔ L) := by
      rw [hsF, secSub_commSec_oTwoRes D hsec hQ, hFA]
    exact le_antisymm ((secSub_le_secSub_iff D hsec hQ hFN hLFA).mp h1.le)
      ((secSub_le_secSub_iff D hsec hQ (EvenMod.commSec_le hsec (oTwoRes_le X)) hLF).mp h1.ge)
  obtain ⟨hinf, hsup⟩ := EvenMod.inf_sup_of_isCompl D hsec hQ hLC hCN hLF hFN
    (by rw [hsC, hsF]; exact hcompl)
  have hCidx : C.relIndex N = 16 := by
    rw [← index_fixW_secMod D hsec hQ le_rfl, EvenMod.bar_self]
    exact hC16
  have hFcard : L.relIndex F = 16 := by
    rw [← card_commW_secMod D hsec hQ le_rfl, EvenMod.bar_self]
    exact hF16
  have hNL : L.relIndex N = L.relIndex C * 16 := by
    rw [← card_secMod D hsec hQ, ← card_secSub D hsec hQ hCN, hsC, ← hC16]
    exact (Subgroup.card_mul_index _).symm
  have hXF : X ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_of_isInvSub_secSub D hsec hQ hLF hFN (by rw [hsF]; exact isInvSub_commW_top W)
  obtain ⟨eR⟩ := restrict_secSub_iso D hsec hQ hLF hFN hXF
  have eO : (secMod D (EvenMod.isSec_of_le hsec hLF hFN hXF)
      ((Subgroup.commutator_mono hFN le_rfl).trans hQ)).Iso orth :=
    (eR.trans (EvenMod.restrictCongr W hsF _ _)).trans eF
  have hcF : cSecIn X L F ≤ pCoreOf 2 X :=
    (secMod_faithful_iff D _ _).mp (EvenMod.faithful_of_iso eO.symm EvenMod.orth_faithful)
  exact ⟨hsw, hCeq, hFeq, hinf, hsup, hCidx, hFcard, hNL,
    isModelSec_of_iso_secMod D _ _ eO.symm hcF⟩

theorem iso_orth_of_isOrthSec (D : Dict5 X P Z) (hsec : IsSec X L N)
    (hQ : ⁅N, pCoreOf 2 X⁆ ≤ L) (h : IsOrthSec X L N) : Nonempty ((secMod D hsec hQ).Iso orth) := by
  set W := secMod D hsec hQ with hW
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := h
  have hcard : Nat.card W.W = 16 := by
    rw [card_secMod, hsd.relIndex_eq, card_orth]
  have hc : cSecIn X L N ≤ pCoreOf 2 X := by
    have hle : D.ψ.ker ≤ θ.ker := by
      rw [hθk]
      exact ker_le_cSecIn D hsec hQ
    have h120 : ∀ φ : ↥X →* Perm (Fin 5), Function.Surjective φ → φ.ker.index = 120 := by
      intro φ hφ
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top, Nat.card_perm,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have hmul := Subgroup.relIndex_mul_index hle
    rw [h120 θ hθs, h120 D.ψ D.surj] at hmul
    have h1 : D.ψ.ker.relIndex θ.ker = 1 := by omega
    have h2 := Subgroup.relIndex_eq_one.mp h1
    intro g hg
    have hgX : g ∈ X := EvenMod.cSecIn_le X L N hg
    have h3 : (⟨g, hgX⟩ : ↥X) ∈ θ.ker := by rw [hθk]; exact hg
    have h4 := h2 h3
    rw [MonoidHom.mem_ker, D.ker_iff] at h4
    exact h4
  have hf : W.Faithful := (secMod_faithful_iff D hsec hQ).mpr hc
  obtain ⟨y, hy⟩ := hθs (swap 0 1)
  have ht : idx W (D.ψ y) = 2 := by
    have h1 := idx_secMod D hsec hQ y.2
    rw [hsd.secIdx_eq_idx hsec.le y.2, hy] at h1
    rw [h1]
    exact ((transvections _ (by decide)).2).mpr ⟨0, 1, by decide, rfl⟩
  obtain ⟨-, -, -, hcompl, hC16, -, ⟨eF⟩⟩ := S18_model W hf ht
  have hfix : fixW W ⊤ = ⊥ := by
    have h1 := Subgroup.card_mul_index (fixW W ⊤)
    rw [hC16, hcard] at h1
    exact Subgroup.eq_bot_of_card_le _ (by omega)
  have htop : commW W ⊤ ⊤ = ⊤ := by
    have h1 := hcompl.sup_eq_top
    rwa [hfix, bot_sup_eq] at h1
  exact ⟨(W.isoRestrictTop _ (isInvSub_commW_top W) htop).trans eF⟩

end CFSG.Quasithin.F53.Stellmacher.S43.Even
