module

public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleChief
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleConj
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleLemmaO
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleOrthZ2
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleProp39

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem o5a_commutator_mem_z1 {V Zg Zy Z1 A : Subgroup G} {c : G}
    (hVab : IsElemAbelian 2 V) (hAab : IsElemAbelian 2 A)
    (hV : V = Zy ⊔ (V ⊓ A)) (hZyV : Zy ≤ V) (hZgV : Zg ≤ V)
    (hint : Zg ⊓ Zy = Z1) (hcA : c ∈ A)
    (hcNg : c ∈ Subgroup.normalizer (Zg : Set G))
    (hcNy : c ∈ Subgroup.normalizer (Zy : Set G))
    {z : G} (hz : z ∈ Zg) : z * c * z⁻¹ * c⁻¹ ∈ Z1 := by
  have hVAN : V ⊓ A ≤ Subgroup.normalizer (Zy : Set G) := by
    intro x hx
    exact Subgroup.centralizer_le_normalizer (Zy : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (hVab.1.is_comm.comm ⟨y, hZyV hy⟩ ⟨x, hx.1⟩))
  obtain ⟨z', hz', a, ha, hza⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (H := Zy) (K := V ⊓ A) hVAN).mp
      (hV ▸ hZgV hz)
  have hca : c * a = a * c :=
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨c, hcA⟩ ⟨a, ha.2⟩)
  have hac : a * c * a⁻¹ = c := by
    rw [← hca]
    group
  have heq : z * c * z⁻¹ * c⁻¹ = z' * c * z'⁻¹ * c⁻¹ := by
    rw [hza]
    calc (z' * a) * c * (z' * a)⁻¹ * c⁻¹
        = z' * (a * c * a⁻¹) * z'⁻¹ * c⁻¹ := by group
      _ = z' * c * z'⁻¹ * c⁻¹ := by rw [hac]
  have hmemZy : z * c * z⁻¹ * c⁻¹ ∈ Zy := by
    rw [heq]
    exact CFSG.Quasithin.H13.A7.commutator_mem_of_mem_normalizer hcNy ⟨z', hz'⟩
  have hmemZg : z * c * z⁻¹ * c⁻¹ ∈ Zg :=
    CFSG.Quasithin.H13.A7.commutator_mem_of_mem_normalizer hcNg ⟨z, hz⟩
  rw [← hint]
  exact Subgroup.mem_inf.mpr ⟨hmemZg, hmemZy⟩

private theorem o5a_mem_normalizer_conj_z2 {L1 L2 S : Subgroup G} {c h : G}
    (hcQ : c ∈ Q1 L1 L2 S) (hh : h ∈ P1 L1 L2 S)
    (hQ1B : Q1 L1 L2 S ≤ bigB L1 L2 S)
    (hBZ2 : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G)) :
    c ∈ Subgroup.normalizer (MulAut.conj h • Z2 L1 L2 S : Subgroup G) := by
  have hhQ : h⁻¹ * c * h⁻¹⁻¹ ∈ Q1 L1 L2 S := by
    simpa using (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S) ((P1 L1 L2 S).inv_mem hh)) c).mp hcQ
  have hN := (CFSG.Quasithin.H13.A7.mem_normalizer_conj_smul_iff
    (V := Z2 L1 L2 S) (g := h⁻¹) (x := c)).mpr (hBZ2 (hQ1B hhQ))
  simpa using hN

private theorem o5as_mem_normalizer_conj_z2 {L1 L2 S : Subgroup G}
    {g y c : G} (hF : F112Hyp L1 L2 S)
    (hg : g ∈ P1 L1 L2 S) (hy : y ∈ P1 L1 L2 S) (hcQ : c ∈ Q1 L1 L2 S) :
    c ∈ Subgroup.normalizer (MulAut.conj g • Z2 L1 L2 S : Subgroup G) ∧
      c ∈ Subgroup.normalizer (MulAut.conj y • Z2 L1 L2 S : Subgroup G) := by
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ1B : Q1 L1 L2 S ≤ bigB L1 L2 S :=
    hQ1S.trans (le_sup_right : S ≤ bigB L1 L2 S)
  have hBZ2 : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
      ((le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
        (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S)))
  exact ⟨o5a_mem_normalizer_conj_z2 hcQ hg hQ1B hBZ2,
    o5a_mem_normalizer_conj_z2 hcQ hy hQ1B hBZ2⟩

private theorem o5as_mem_conj_s {L1 L2 S : Subgroup G} {g c : G}
    (hF : F112Hyp L1 L2 S) (hg : g ∈ P1 L1 L2 S) (hcQ : c ∈ Q1 L1 L2 S) :
    c ∈ MulAut.conj g • S := by
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hmem : g⁻¹ * c * g⁻¹⁻¹ ∈ S := by
    simpa using hQ1S ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (P1 L1 L2 S) ((P1 L1 L2 S).inv_mem hg)) c).mp hcQ)
  simpa using (CFSG.Quasithin.H13.A7.mem_conj_smul_iff (V := S) (g := g⁻¹) (x := c)).mpr hmem

private theorem o5as_range_commutator_subset {V Zg Zy Z1 A : Subgroup G} {c : G}
    (hVab : IsElemAbelian 2 V) (hAab : IsElemAbelian 2 A)
    (hV : V = Zy ⊔ (V ⊓ A)) (hZyV : Zy ≤ V) (hZgV : Zg ≤ V)
    (hint : Zg ⊓ Zy = Z1) (hcA : c ∈ A)
    (hcNg : c ∈ Subgroup.normalizer (Zg : Set G))
    (hcNy : c ∈ Subgroup.normalizer (Zy : Set G)) :
    Set.range (fun v : ↥Zg => (v : G) * c * (v : G)⁻¹ * c⁻¹) ⊆ (Z1 : Set G) := by
  rintro - ⟨v, rfl⟩
  exact o5a_commutator_mem_z1 hVab hAab hV hZyV hZgV hint hcA hcNg hcNy v.2

private theorem o5as_relIndex_le_two_pow {V Zg Zy Z1 A : Subgroup G} {c : G} {l : ℕ}
    (hVab : IsElemAbelian 2 V) (hAab : IsElemAbelian 2 A)
    (hV : V = Zy ⊔ (V ⊓ A)) (hZyV : Zy ≤ V) (hZgV : Zg ≤ V)
    (hint : Zg ⊓ Zy = Z1) (hcA : c ∈ A)
    (hcNg : c ∈ Subgroup.normalizer (Zg : Set G))
    (hcNy : c ∈ Subgroup.normalizer (Zy : Set G))
    (hZ1 : Nat.card Z1 = 2 ^ l) :
    (Subgroup.centralizer ({c} : Set G)).relIndex Zg ≤ 2 ^ l := by
  have hcomm : ∀ v ∈ Zg, ∀ w ∈ Zg, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hVab.1.is_comm.comm ⟨v, hZgV hv⟩ ⟨w, hZgV hw⟩)
  have hsub := o5as_range_commutator_subset hVab hAab hV hZyV hZgV hint hcA hcNg hcNy
  have hcard := CFSG.Quasithin.H13.A7.card_range_commutator_eq_relIndex
    (V := Zg) hcomm hcNg
  rw [← hcard]
  calc Nat.card (Set.range fun v : Zg => (v : G) * c * (v : G)⁻¹ * c⁻¹)
      ≤ Nat.card Z1 := Nat.card_mono (Set.toFinite _) hsub
    _ = 2 ^ l := hZ1

private theorem o5as_relIndex_le {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    {g c : G} (hDS : Subgroup.zpowers c ≤ MulAut.conj g • S)
    (hDQ : ¬ Subgroup.zpowers c ≤ MulAut.conj g • Q2 L1 L2 S) :
    2 ^ l * (MulAut.conj g • Q2 L1 L2 S).relIndex (Subgroup.zpowers c) ≤
      (Subgroup.centralizer ({c} : Set G)).relIndex (MulAut.conj g • Z2 L1 L2 S) := by
  have hT := str86_orth_pow_mul_relIndex_le_conj (L1 := L1) (L2 := L2) (S := S) (m := m)
    hF hSB hm hL2 hstepW hWZ2 hE e hl hml horth (g := g) (D := Subgroup.zpowers c) hDS hDQ
  have hcent : Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rwa [hcent] at hT

theorem str86_orth_step9_false {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x)
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ l)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) {g y : G} (hg : g ∈ P1 L1 L2 S)
    (hy : y ∈ P1 L1 L2 S)
    (hV : conjClosure (Z2 L1 L2 S) L1 =
      MulAut.conj y • Z2 L1 L2 S ⊔ (conjClosure (Z2 L1 L2 S) L1 ⊓ A))
    (hint : MulAut.conj g • Z2 L1 L2 S ⊓ MulAut.conj y • Z2 L1 L2 S = Z1 L1 L2 S)
    {c : G} (hcA : c ∈ A) (hcQ : c ∈ Q1 L1 L2 S) (hcg : c ∉ MulAut.conj g • Q2 L1 L2 S) :
    False := by
  classical
  obtain ⟨hVab, -, -, hconj⟩ := str86_conjClosure_basics hF hSB hZQ hab
  obtain ⟨hcNg0, hcNy0⟩ := o5as_mem_normalizer_conj_z2 hF hg hy hcQ
  have hcSg : c ∈ MulAut.conj g • S := o5as_mem_conj_s hF hg hcQ
  set V : Subgroup G := conjClosure (Z2 L1 L2 S) L1 with hVdef
  set Zg : Subgroup G := MulAut.conj g • Z2 L1 L2 S with hZgdef
  set Zy : Subgroup G := MulAut.conj y • Z2 L1 L2 S with hZydef
  set Qg : Subgroup G := MulAut.conj g • Q2 L1 L2 S with hQgdef
  have hcNg : c ∈ Subgroup.normalizer (Zg : Set G) := by simpa [hZgdef] using hcNg0
  have hcNy : c ∈ Subgroup.normalizer (Zy : Set G) := by simpa [hZydef] using hcNy0
  have hZgV : Zg ≤ V := by simpa [hZgdef, hVdef] using hconj g hg
  have hZyV : Zy ≤ V := by simpa [hZydef, hVdef] using hconj y hy
  have hV' : V = Zy ⊔ (V ⊓ A) := by simpa [hVdef, hZydef] using hV
  have hint' : Zg ⊓ Zy = Z1 L1 L2 S := by simpa [hZgdef, hZydef] using hint
  have hle2 : (Subgroup.centralizer ({c} : Set G)).relIndex Zg ≤ 2 ^ l :=
    o5as_relIndex_le_two_pow hVab hA.2.1 hV' hZyV hZgV hint' hcA hcNg hcNy hZ1
  have hDS : Subgroup.zpowers c ≤ MulAut.conj g • S := by
    rw [Subgroup.zpowers_le]
    exact hcSg
  have hDQ : ¬ Subgroup.zpowers c ≤ MulAut.conj g • Q2 L1 L2 S := by
    intro h
    exact hcg (h (Subgroup.mem_zpowers c))
  have hT := o5as_relIndex_le hF hSB hm hL2 hstepW hWZ2 hE e hl hml horth hDS hDQ
  change 2 ^ l * Qg.relIndex (Subgroup.zpowers c) ≤
    (Subgroup.centralizer ({c} : Set G)).relIndex Zg at hT
  have hrel1 : Qg.relIndex (Subgroup.zpowers c) ≠ 1 := by
    intro h
    exact hcg (Subgroup.relIndex_eq_one.mp h (Subgroup.mem_zpowers c))
  have hrel0 : Qg.relIndex (Subgroup.zpowers c) ≠ 0 :=
    CFSG.Quasithin.D15Proof.relIndex_ne_zero _ _
  have hrel2 : 2 ≤ Qg.relIndex (Subgroup.zpowers c) := by omega
  have hmul : 2 ^ l * 2 ≤ 2 ^ l * Qg.relIndex (Subgroup.zpowers c) :=
    Nat.mul_le_mul_left _ hrel2
  have hfin : 2 ^ l * 2 ≤ 2 ^ l := hmul.trans (hT.trans hle2)
  have hpos : 0 < 2 ^ l := pow_pos (by norm_num) l
  omega

private theorem o5s_z2_z1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) :
    Z2 L1 L2 S = W ∧ W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S ∧
      Nat.card (Z1 L1 L2 S) = 2 ^ l := by
  classical
  have hZ2 : Z2 L1 L2 S = W :=
    str86_orth_z2_eq_commutator hF hSB hk hFc hU3 hB2 hm hL2 hZI hstepW hWZ2 hcomm
      hE e hl hml horth
  have hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S := by
    rw [← hcomm]
    exact (str86_z1_le_commutator hF hSB hk hFc hU3 hB2 hm hL2 hZI).2
  exact ⟨hZ2, hWS,
    str86_card_z1_of_orth hF hSB hm hL2 hstepW hE e hl hml horth hWS⟩

private theorem o5s_exists_maxElemAbelian
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ¬ A ≤ Q1 L1 L2 S ∧
      A ≤ Q2 L1 L2 S ∧ Z2 L1 L2 S ≤ A := by
  classical
  have hJQ2 : thompsonJ S ≤ Q2 L1 L2 S :=
    iSup₂_le fun E hEmax =>
      str86_orth_le_q2_of_isMaxElemAbelian hF hSB hk hFc hU3 hB2 hm hL2 hZI
        hstepW hWZ2 hE e hl hml horth hEmax
  have hJnotQ1 : ¬ thompsonJ S ≤ Q1 L1 L2 S := by
    intro hJ1
    exact str86_not_thompsonJ_le_q1_inf_q2 hF hSB (le_inf hJ1 hJQ2)
  obtain ⟨A, hAmax, hAnQ1⟩ :=
    Ch3g316.exists_isMaxElemAbelian_not_le_pCoreOf (T := S) (Q := Q1 L1 L2 S) hJnotQ1
  have hAQ2 : A ≤ Q2 L1 L2 S :=
    str86_orth_le_q2_of_isMaxElemAbelian hF hSB hk hFc hU3 hB2 hm hL2 hZI
      hstepW hWZ2 hE e hl hml horth hAmax
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hZ2S : Z2 L1 L2 S ≤ S :=
    (CFSG.Quasithin.A4.omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S
  have hZ2C : Z2 L1 L2 S ≤ Subgroup.centralizer (A : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp
      (CFSG.Quasithin.A4.centerOf_le_centralizer (Q2 L1 L2 S)
        (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf (Q2 L1 L2 S) hz))
      a (hAQ2 ha)
  have hZA : Z2 L1 L2 S ≤ A := by
    intro z hz
    exact CFSG.QuasithinUnique.Setup.Campbell.maxElem_mem_of_centralizer hAmax
      (hZ2S hz) (hZ2C hz) (CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf hz)
  exact ⟨A, hAmax, hAnQ1, hAQ2, hZA⟩

private theorem o5s_exists_g
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x)
    {A : Subgroup G} (hAmax : IsMaxElemAbelian S A) (hAnQ1 : ¬ A ≤ Q1 L1 L2 S)
    (hAQ2 : A ≤ Q2 L1 L2 S) :
    ∃ g ∈ L1, g ∉ bigB L1 L2 S ∧
      ¬ A ⊓ Q1 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S := by
  classical
  obtain ⟨g, hgL1, hgA⟩ :=
    str86_exists_conj_not_le hF hSB hk hFc hU3 hZQ hab hAmax hAnQ1
  refine ⟨g, hgL1, ?_, hgA⟩
  intro hgBin
  apply hgA
  have hgP2 : g ∈ P2 L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hgBin
  have hQ2fix : MulAut.conj g • Q2 L1 L2 S = Q2 L1 L2 S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S) hgP2)
  rw [hQ2fix]
  exact inf_le_left.trans hAQ2

private theorem o5s_exists_y_c
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    {A : Subgroup G} (hAmax : IsMaxElemAbelian S A) (hAnQ1 : ¬ A ≤ Q1 L1 L2 S)
    {g : G} (hgP1 : g ∈ P1 L1 L2 S) (hgB : g ∉ bigB L1 L2 S)
    (hgA : ¬ A ⊓ Q1 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S) :
    ∃ y c : G, y ∈ P1 L1 L2 S ∧ g⁻¹ * y ∉ bigB L1 L2 S ∧
      c ∈ A ⊓ Q1 L1 L2 S ∧ c ∉ MulAut.conj g • Q2 L1 L2 S ∧
      ¬ A ⊓ Q1 L1 L2 S ≤ MulAut.conj y • Q2 L1 L2 S := by
  classical
  obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hAnQ1
  have haS : a ∈ S := hAmax.1 haA
  have hgR1 : g⁻¹ * a * g ∉ bigB L1 L2 S :=
    str86_conj_not_mem_bigB hF hSB hk hFc hU3 hgP1 hgB haS haQ
  set y : G := a * g with hy_def
  have haP1 : a ∈ P1 L1 L2 S :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) haS)
  have hyP1 : y ∈ P1 L1 L2 S := by
    rw [hy_def]
    exact (P1 L1 L2 S).mul_mem haP1 hgP1
  have hgy : g⁻¹ * y ∉ bigB L1 L2 S := by
    rw [hy_def]
    simpa [mul_assoc] using hgR1
  obtain ⟨c, hcAQ, hcg⟩ := Set.not_subset.mp hgA
  have hAy : ¬ A ⊓ Q1 L1 L2 S ≤ MulAut.conj y • Q2 L1 L2 S := by
    intro hle
    have hcy : c ∈ MulAut.conj y • Q2 L1 L2 S := hle hcAQ
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hcy
    rw [MulAut.smul_def, MulAut.conj_inv_apply] at hcy
    apply hcg
    change c ∈ MulAut.conj g • Q2 L1 L2 S
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
    have hca : a * c = c * a :=
      CFSG.Open.IsElemAbelian.comm hAmax.2.1 haA (Subgroup.mem_inf.mp hcAQ).1
    have hconjy : y⁻¹ * c * y = g⁻¹ * c * g := by
      rw [hy_def]
      have h1 : a⁻¹ * c * a = c := by
        calc a⁻¹ * c * a = a⁻¹ * (c * a) := by group
          _ = a⁻¹ * (a * c) := by rw [hca.symm]
          _ = c := by group
      calc (a * g)⁻¹ * c * (a * g) = g⁻¹ * (a⁻¹ * c * a) * g := by group
        _ = g⁻¹ * c * g := by rw [h1]
    rw [hconjy] at hcy
    exact hcy
  exact ⟨y, c, hyP1, hgy, hcAQ, hcg, hAy⟩

private theorem o5s_conjClosure_and_relIndex
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : 2 ≤ m) (hkm : 2 * k ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x)
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    {A : Subgroup G} (hAmax : IsMaxElemAbelian S A) {g y : G}
    (hgP1 : g ∈ P1 L1 L2 S)
    (hgA : ¬ A ⊓ Q1 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S)
    (hyP1 : y ∈ P1 L1 L2 S)
    (hAy : ¬ A ⊓ Q1 L1 L2 S ≤ MulAut.conj y • Q2 L1 L2 S) :
    (conjClosure (Z2 L1 L2 S) L1 =
      MulAut.conj y • Z2 L1 L2 S ⊔ (conjClosure (Z2 L1 L2 S) L1 ⊓ A)) ∧
      2 * 2 ^ l ≤
        (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S) := by
  classical
  obtain ⟨hlk, -, hidxg, h2k⟩ :=
    str86_orth_chain hF hSB hk hFc hU3 hL2 hkm hZQ hab hstepW hWZ2 hE e hl hml
      horth hAmax hgP1 hgA
  obtain ⟨-, hAQy, hidxy, -⟩ :=
    str86_orth_chain hF hSB hk hFc hU3 hL2 hkm hZQ hab hstepW hWZ2 hE e hl hml
      horth hAmax hyP1 hAy
  have hV := str86_orth_conjClosure_eq_sup hF hSB hk hFc hU3 hB2 hm hL2 hZI hZQ hab
    hstepW hWZ2 hE e hl hml horth hAmax hyP1 hAQy hidxy
  refine ⟨hV, ?_⟩
  simpa [hlk] using h2k

private theorem o5s_conj_inf_eq_z1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e))
    (hWS : W ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S)
    (hZ2 : Z2 L1 L2 S = W) {A : Subgroup G} (hZA : Z2 L1 L2 S ≤ A)
    {g y : G} (hgP1 : g ∈ P1 L1 L2 S) (hyP1 : y ∈ P1 L1 L2 S)
    (hgy : g⁻¹ * y ∉ bigB L1 L2 S)
    (hidx : 2 * 2 ^ l ≤
      (MulAut.conj g • Z2 L1 L2 S ⊓ A).relIndex (MulAut.conj g • Z2 L1 L2 S)) :
    MulAut.conj g • Z2 L1 L2 S ⊓ MulAut.conj y • Z2 L1 L2 S = Z1 L1 L2 S := by
  classical
  have hI := str86_orth_iInf_eq_z1 hF hSB hm hL2 hstepW hE e hl hml horth
    hWS hZ2 hZA hgP1 hidx
  have hBNZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S))).trans
      (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  have hQ2CZ : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp
      (CFSG.Quasithin.A4.centerOf_le_centralizer (Q2 L1 L2 S)
        (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf (Q2 L1 L2 S) hz))
      q hq).symm
  rw [str86_conj_inf_conj_eq_iInf hF hSB hk hFc hU3 hm hL2 hBNZ hQ2CZ
    hgP1 hyP1 hgy, hI]

theorem str86_orth_false
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hkm : 2 * k ≤ m)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x)
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) :
    False := by
  classical
  have hm : 2 ≤ m := by omega
  obtain ⟨hZ2, hWS, hZ1⟩ :=
    o5s_z2_z1 hF hSB hk hFc hU3 hB2 hm hL2 hZI hstepW hWZ2 hcomm hE e hl hml horth
  obtain ⟨A, hAmax, hAnQ1, hAQ2, hZA⟩ :=
    o5s_exists_maxElemAbelian hF hSB hk hFc hU3 hB2 hm hL2 hZI hstepW hWZ2 hE e
      hl hml horth
  obtain ⟨g, hgL1, hgB, hgA⟩ :=
    o5s_exists_g hF hSB hk hFc hU3 hZQ hab hAmax hAnQ1 hAQ2
  have hgP1 : g ∈ P1 L1 L2 S := (le_sup_left : L1 ≤ P1 L1 L2 S) hgL1
  obtain ⟨y, c, hyP1, hgy, hcAQ, hcg, hAy⟩ :=
    o5s_exists_y_c hF hSB hk hFc hU3 hAmax hAnQ1 hgP1 hgB hgA
  obtain ⟨hV, hidx4⟩ :=
    o5s_conjClosure_and_relIndex hF hSB hk hFc hU3 hB2 hm hkm hL2 hZI hZQ hab
      hstepW hWZ2 hE e hl hml horth hAmax hgP1 hgA hyP1 hAy
  have hint := o5s_conj_inf_eq_z1 hF hSB hk hFc hU3 hm hL2 hstepW hE e hl hml horth
    hWS hZ2 hZA hgP1 hyP1 hgy hidx4
  exact str86_orth_step9_false hF hSB hm hL2 hZQ hab hstepW hWZ2 hE e hl hml
    horth hZ1 hAmax hgP1 hyP1 hV hint (Subgroup.mem_inf.mp hcAQ).1
    (Subgroup.mem_inf.mp hcAQ).2 hcg

end CFSG.Quasithin.Stroth

end
