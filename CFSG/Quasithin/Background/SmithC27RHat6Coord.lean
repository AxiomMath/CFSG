module

public import CFSG.Quasithin.Background.SmithC27RHat6Lin
public import CFSG.Quasithin.Background.SmithC27B51
public import CFSG.Quasithin.Background.C124BlkHat6

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

theorem inf_centralizer_le_centralizer_blockU (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hK : IsShort2 K) :
    K ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (blockU K : Set G) := by
  intro x hx
  have hU : blockU K ≤ Subgroup.centralizer {x} := by
    rw [blockU_eq_sup h hs hK]
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hx.2 u (commutator_V_K_le_V hs hu)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hu.2 x hx.1).symm
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact Subgroup.mem_centralizer_singleton_iff.1 (hU hu)

theorem inf_centralizer_eq_of_hatA6 (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hB : IsHatA6Block K) : K ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 K := by
  refine le_antisymm (fun x hx => ?_) (le_inf (pCoreOf_le 2 K) hs.pCore_K_le_centralizer)
  rw [← hB.2.2.2]
  exact ⟨hx.1, inf_centralizer_le_centralizer_blockU h hs hB.1 hx⟩

@[expose] noncomputable def starK (hs : StarHyp R K V) : ↥K →* ↥(autOn K V) :=
  C124.starHom hs.elemAbelian K hs.K_le_normalizer_V

omit [Finite G] in
theorem coe_starK (hs : StarHyp R K V) (k : ↥K) :
    ((starK hs k : ↥(autOn K V)) : MulAut ↥V) = conjAct V ⟨k, hs.K_le_normalizer_V k.2⟩ := rfl

theorem starK_surjective (hs : StarHyp R K V) : Function.Surjective (starK hs) :=
  C124.starHom_surjective hs.elemAbelian hs.K_le_normalizer_V

noncomputable def autOnEquivOfHatA6 (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hB : IsHatA6Block K) : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(autOn K V) :=
  (QuotientGroup.quotientMulEquivOfEq (C124.ker_starHom_eq_pCore hs.elemAbelian
      hs.K_le_normalizer_V (inf_centralizer_eq_of_hatA6 h hs hB).symm).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (C124.starHom_surjective hs.elemAbelian hs.K_le_normalizer_V))

theorem isHat_autOn_of_hatA6 (h : Hyp27 H R M K) (hs : StarHyp R K V) (hB : IsHatA6Block K) :
    IsHat ↥(autOn K V) ↥(alternatingGroup (Fin 6)) :=
  IsHat.of_mulEquiv (autOnEquivOfHatA6 h hs hB) hB.2.1

theorem card_autOn_of_hatA6 (h : Hyp27 H R M K) (hs : StarHyp R K V) (hB : IsHatA6Block K) :
    Nat.card ↥(autOn K V) = 1080 :=
  card_of_isHat_alt6 (isHat_autOn_of_hatA6 h hs hB)

theorem exists_coord_of_hatA6 (h : Hyp27 H R M K) (hs : StarHyp R K V) (hB : IsHatA6Block K)
    (hT : ∃ hV : IsElemAbelian 2 V,
      TripleA6Six (autI hV K) (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K))) :
    blockZ K = ⊥ ∧ blockU K ≤ V ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 4 ∧
        ∃ ψ : ↥(autOn K V) →* Matrix.GeneralLinearGroup (Fin 3) F, Function.Injective ψ ∧
          ∃ e : ↥(blockU K) ≃* Multiplicative (Fin 3 → F),
            ∀ (k : ↥K) (u v : ↥(blockU K)), (v : G) = k * u * k⁻¹ →
              Multiplicative.toAdd (e v) =
                ((ψ (starK hs k) : Matrix.GeneralLinearGroup (Fin 3) F) :
                  Matrix (Fin 3) (Fin 3) F).mulVec
                  (Multiplicative.toAdd (e u)) := by
  obtain ⟨hV, F, hF, hFfin, Γ₀, hF4, -, hHat0, -, hR⟩ := hT
  obtain ⟨π, hπ⟩ : ∃ π : ↥Γ₀ →* ↥(autI hV K), (FFModel.nat Γ₀).RealizesVia (autI hV K)
      (commV (autI hV K)) (fixV (autI hV K) ⊓ commV (autI hV K)) π := hR
  have hKV := hs.K_le_normalizer_V
  obtain ⟨β, hβs, hβk, hβe⟩ := C124.exists_blockHomNat hV hKV (commutator_V_K_le_blockU h hs)
    (blockU_eq_sup h hs hB.1) Γ₀ π hπ
  have hβb : Function.Bijective β := hβs.bijective_of_nat_card_le (by
    rw [hB.2.2.1, C124.card_threeSpace hF4]; norm_num)
  have hZ : blockZ K = ⊥ := by
    have hk : β.ker = ⊥ := (MonoidHom.ker_eq_bot_iff β).2 hβb.1
    rw [hβk, Subgroup.subgroupOf_eq_bot] at hk
    exact disjoint_self.1 (hk.mono_right inf_le_left)
  have hUV : blockU K ≤ V := by
    rw [blockU_eq_sup h hs hB.1, hZ, sup_bot_eq]
    exact commutator_V_K_le_V hs
  have hπs : Function.Surjective (π : ↥Γ₀ → ↥(autI hV K)) := hπ.1
  have hπb : Function.Bijective π := hπs.bijective_of_nat_card_le (by
    rw [card_of_isHat_alt6 hHat0]
    exact (card_autOn_of_hatA6 h hs hB).ge)
  let πe : ↥Γ₀ ≃* ↥(autI hV K) := MulEquiv.ofBijective π hπb
  let _ : Fintype F := Fintype.ofFinite F
  refine ⟨hZ, hUV, F, hF, inferInstance, by rw [Fintype.card_eq_nat_card]; exact hF4,
    Γ₀.subtype.comp πe.symm.toMonoidHom, Γ₀.subtype_injective.comp πe.symm.injective,
    MulEquiv.ofBijective β hβb, fun k u v huv => ?_⟩
  exact hβe k (πe.symm (C124.starHom hV K hKV k)) (πe.apply_symm_apply _) u v huv

end CFSG.Quasithin.SmithC27
