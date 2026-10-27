module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseLabel
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseN
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitPos
import CFSG.LocalAnalysis.StandardType.GGQTwoPThree
import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryRk1Aux

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

variable {G : Type} [Group G] [Finite G]


theorem ggQTwoDUnit_base_of_member (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) {m : ℕ} (e' : Fin m ≃ ι) (hm : 5 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hU : GGMemberUnitary p Bs L) :
    ∃ (F0 : Type) (_ : Field F0) (_ : Finite F0) (_ : CharP F0 2) (ψ : Su F0 2 1 m →* G)
      (ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)), QTwoUnitBase p B Bs x L ψ ε := by
  obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
  have hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e := hcfg.2.2.2.1
  have hp3 : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hpres hr hrc h6
  subst p
  obtain ⟨K, hKf, hKfin, hKchar, f, n, ψ, hhyp, hrange, hdiag, ε, hperm, hrefl, hrankOne⟩ :=
    ggQTwoDUnit_position hcfg.1 (Or.inl rfl) hU
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hBs : IsElemAbelian 3 Bs := hcfg.1.1.1.2.1.2.1
  have hrefl_r : GGIsReflection 3 r := ggCoxRefl_isReflection hpres.2 hrc
  obtain ⟨a, b, hab, hr_eq⟩ := ggMUR1_refl_eq_swap hp hp2 hBs ε hrefl hr hrefl_r
  have h6' : Nat.card ↥((ggSuPairBlock K 2 f n a b).map ψ) = 6 := by
    rw [← hrankOne a b hab, ← hr_eq]
    exact h6
  have hf : f = 1 := ggQTwoDUnit_f_eq_one hhyp hab h6'
  subst f
  have hn : n = m :=
    ggQTwoDUnit_base_n_eq hTBF hWI hcfg rfl e' hm hM hhyp hrange hdiag ε hperm hrefl
  subst n
  have hcardK : Nat.card K = 4 := by
    rw [hhyp.card]
    norm_num
  have hcard : Nat.card ↥Bs = 3 ^ m := by
    obtain ⟨β, -⟩ := ggQTwoD_selectedModule hTBF hWI hcfg e' (by omega) hM
    calc Nat.card ↥Bs = Nat.card (DVec m) := Nat.card_congr (Additive.ofMul.trans β.toEquiv)
      _ = 3 ^ m := by
        rw [Nat.card_pi]
        simp
  obtain ⟨hxmem, hxord, hcent⟩ := ggQTwoDUnit_base_cent hcfg rfl
  have hfull : ∀ c : Fin m → Kˣ, ∃ b ∈ Bs, qTwoChartTwoThree_induces ψ b c :=
    ggQTwoDUnit_base_full hcardK hhyp hrange hdiag hcard hcent hxord
  exact ⟨K, hKf, hKfin, hKchar, ψ, ε,
    ⟨rfl, hcardK, hhyp, hrange, hdiag, hperm, hrefl, hrankOne, hcard, hxmem, hxord, hcent,
      hfull⟩⟩

theorem ggQTwoDUnit_member_ne_six (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) {m : ℕ} (e' : Fin m ≃ ι) (hm : 5 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hU : GGMemberUnitary p Bs L) : m ≠ 6 := by
  obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
  have hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e := hcfg.2.2.2.1
  have hp3 : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hpres hr hrc h6
  subst p
  obtain ⟨K, hKf, hKfin, hKchar, f, n, ψ, hne, hhyp, hrange, hdiag, ε, hperm, hrefl, hrankOne⟩ :=
    ggQTwoDUnit_position_ne hcfg.1 (Or.inl rfl) hU
  have hBs : IsElemAbelian 3 Bs := hcfg.1.1.1.2.1.2.1
  obtain ⟨a, b, hab, hr_eq⟩ := ggMUR1_refl_eq_swap Nat.prime_three (by norm_num) hBs ε hrefl hr
    (ggCoxRefl_isReflection hpres.2 hrc)
  have hf : f = 1 := ggQTwoDUnit_f_eq_one hhyp hab (by
    rw [← hrankOne a b hab, ← hr_eq]
    exact h6)
  subst f
  have hn : n = m :=
    ggQTwoDUnit_base_n_eq hTBF hWI hcfg rfl e' hm hM hhyp hrange hdiag ε hperm hrefl
  exact fun h6' => hne ⟨rfl, Or.inr (hn.trans h6')⟩

theorem ggQTwoDUnit_u62_of_six (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (e' : Fin 6 ≃ ι) (hM : M = (ggCoxeterMatrixD 6).reindex e') (hL : qtwoOrthL.compl G L 𝒦) :
    GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L :=
  ((ggQTwoDUnit_memberUnitary_L_or_u62 hRig hTBF hcfg e' (by norm_num) hM hL).resolve_left
    fun hU => ggQTwoDUnit_member_ne_six hTBF hWI hcfg e' (by norm_num) hM hU rfl).2


theorem ggQTwoDUnit_base_of_ne_six (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hm : 5 ≤ m) (hm6 : m ≠ 6)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hL : qtwoOrthL.compl G L 𝒦) :
    ∃ (F0 : Type) (_ : Field F0) (_ : Finite F0) (_ : CharP F0 2) (ψ : Su F0 2 1 m →* G)
      (ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)), QTwoUnitBase p B Bs x L ψ ε := by
  obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
  have hp3 : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst p
  exact ggQTwoDUnit_base_of_member hTBF hWI hcfg e' hm hM
    (ggQTwoDUnit_memberUnitary_L_of_ne_six hRig hTBF hcfg e' (by omega) hm6 hM hL)

theorem ggQTwoDUnit_base (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hm : 7 ≤ m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hL : qtwoOrthL.compl G L 𝒦) :
    ∃ (F0 : Type) (_ : Field F0) (_ : Finite F0) (_ : CharP F0 2) (ψ : Su F0 2 1 m →* G)
      (ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)), QTwoUnitBase p B Bs x L ψ ε :=
  ggQTwoDUnit_base_of_ne_six hRig hTBF hWI hcfg e' (by omega) (by omega) hM hL

end CFSG.StandardType.QTwo

end
