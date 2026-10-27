module

public import CFSG.LocalAnalysis.StandardType.GGTBTorCentral
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepTwA5RowDefs
public import CFSG.LocalAnalysis.StandardType.GGE6D4TwoNodeLocalInput
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTorusTBAt {G : Type} [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G) : Prop :=
  ∀ (r : ℕ) {R : Type} [Group R] (θ : ↥X ⧸ Subgroup.center ↥X ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
    (∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I) → GGTorusLift p r R →
      GGTorusTBGroup p r R I ↥X (ggQuotHom θ) (ggGamma X hN).range

theorem ggTorusTBAt_L {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hL : commutator ↥L = ⊤) :
    GGTorusTBAt p Bs L :=
  fun _ _ _ θ _ hN hBsI hlift => ggTorusTBGroup_of_L hcfg hL θ hN hBsI hlift

theorem ggTorusTBAt_nbr {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator ↥K = ⊤) : GGTorusTBAt p Bs K :=
  fun _ _ _ θ _ hN hBsI hlift => ggTorusTBGroup_of_nbr hcfg hnb hK θ hN hBsI hlift

theorem ggTorData_of_hasLabel (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {Bs X : Subgroup G} (hInn : GGInnerDiagOn Bs X) (hTB : GGTorusTBAt p Bs X)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X))
    (hW : LargeEvenLabelAll lab fun R _ I _ => GGTorusTorW p r m N C M R I)
    (hLift : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p r R) :
    ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      GGTorusTorData m N C M ↥X (ggGamma X hN).range := by
  have hN : Bs ≤ Subgroup.normalizer (X : Set G) := ggInnerDiagOn_le_normalizer hInn
  have hmark := ggInnerDiagOn_relabel hRig hInn hlab hhas
  have hmark' := largeEvenMarking_and_labelAll (S := fun lab' => lab' = lab)
    (P' := fun R _ I _ => GGTorusTorW p r m N C M R I ∧ GGTorusLift p r R)
    (fun lab' _ h' => by rw [h']; exact largeEvenLabelAll_and hW hLift)
    (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨-, lab', -, hraw'⟩ := hmark'
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨-, -, hind⟩, hWtor, hlift⟩⟩ := largeEvenRawDatum_exists hraw'
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  exact ⟨hN, hWtor ↥X (ggQuotHom θ) (ggGamma X hN).range (hTB r θ hN hBsI hlift)⟩

private lemma ggTI_coxeter_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

theorem ggResXDatumA_ind_of_wit {G : Type} [Group G] [Finite G] {p m n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {Bs X : Subgroup G}
    (hM : GGIsWeylMatrix (CoxeterMatrix.A n))
    (hMC : GGIntCartan (CoxeterMatrix.A n) (CartanMatrix.A n)) (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit m n ↥X (ggGamma X hN).range)
    (hw : w.Holds (CartanMatrix.A n) (CoxeterMatrix.A n)) :
    GGResXDatumA p Bs X n ∧
      ((∀ c : Fin n → ZMod p,
          (List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod = 1 → c = 0) →
        ∀ z : G, GGResXDatumAx p Bs X z n) := by
  obtain ⟨V, hVadd, hVmod, hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  refine ⟨?_, fun hInd z => ?_⟩
  · obtain ⟨hnk, hbk, α, hlin, hpair, -, -⟩ := ggTD_linearData hm hpm hBs hS hN w hw V ι
    obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
    have hcl := ggTD_closure hN hw hp2 hBs hnk
    have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
      intro i
      rw [hpair i i, hMC.1 i]
      norm_num
    refine ⟨Fin n, inferInstance, inferInstance, CoxeterMatrix.A n, CartanMatrix.A n, V, hVadd,
      hVmod, ι, (fun k => ggTDρB X Bs (ggTDnH w hnk k)),
      (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))), α, Equiv.refl _,
      ggTI_coxeter_reindex_refl _, hM, hMC, hlin, ?_, hpair, ⟨e, he⟩, hcl⟩
    intro i
    exact ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))
  · obtain ⟨hnk, hbk, α, hlin, hpair, -, -, hind⟩ := ggTD_lin hm hpm hBs hS hN w hw hInd V ι
    obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
    have hcl := ggTD_closure hN hw hp2 hBs hnk
    have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
      intro i
      rw [hpair i i, hMC.1 i]
      norm_num
    refine ⟨Fin n, inferInstance, inferInstance, CoxeterMatrix.A n, CartanMatrix.A n, V, hVadd,
      hVmod, ι, (fun k => ggTDρB X Bs (ggTDnH w hnk k)),
      (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))), α, Equiv.refl _,
      ggTI_coxeter_reindex_refl _, hM, hMC, hlin, ?_, hpair, ⟨e, he⟩, hcl, fun _ => hind⟩
    intro i
    exact ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))

theorem ggResXDatumE6x_of_wit {G : Type} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {Bs X : Subgroup G}
    (hM : GGIsWeylMatrix CoxeterMatrix.E₆) (hMC : GGIntCartan CoxeterMatrix.E₆ CartanMatrix.E₆)
    (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit m 6 ↥X (ggGamma X hN).range)
    (hw : w.Holds CartanMatrix.E₆ CoxeterMatrix.E₆)
    (hInd : ∀ c : Fin 6 → ZMod p,
      (List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod = 1 → c = 0) (z : G) :
    GGResXDatumE6x p Bs X z := by
  obtain ⟨V, hVadd, hVmod, hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  obtain ⟨hnk, hbk, α, hlin, hpair, -, -, hind⟩ := ggTD_lin hm hpm hBs hS hN w hw hInd V ι
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, hMC.1 i]
    norm_num
  refine ⟨Fin 6, inferInstance, inferInstance, CoxeterMatrix.E₆, CartanMatrix.E₆, V, hVadd,
    hVmod, ι, (fun k => ggTDρB X Bs (ggTDnH w hnk k)),
    (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))), α, Equiv.refl _,
    ggTI_coxeter_reindex_refl _, hM, hMC, hlin, ?_, hpair, ⟨e, he⟩, hcl, fun _ => hind⟩
  intro i
  exact ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))

private theorem ggTI_central {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {X : Subgroup G} {z : G}
    (hzX : z ∈ X) (hzc : z ∈ Subgroup.centralizer (X : Set G)) (hz1 : z ≠ 1) (hzp : z ^ p = 1) :
    (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X ∧ orderOf (⟨z, hzX⟩ : ↥X) = p := by
  refine ⟨Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, ?_⟩
  · simpa using Subgroup.mem_centralizer_iff.mp hzc g g.2
  · refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using hzp)
    · exact fun h => hz1 (congrArg Subtype.val h)

private theorem ggTI_four_le {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 1 ≤ r)
    (hd : p ∣ r + 3) : 4 ≤ r + 2 := by
  by_contra h
  have h1 : r = 1 := by omega
  subst h1
  have h4 : p ∣ 2 * 2 := by simpa using hd
  rcases hp.dvd_mul.mp h4 with h | h <;>
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

theorem ggTwoNodeIndepA_of_tbTor (hRig : GGLabelRigidInput) (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hInn : GGInnerDiagOn Bs X) (hTB : GGTorusTBAt p Bs X) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X))
    (htag : lab.tag = .A ∨ lab.tag = .twA) (h4 : 4 ≤ lab.rank) (hdvd : p ∣ lab.rank + 1)
    (hM : p ∣ ggTorM lab) (hex : ¬ (p = 3 ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n + 1)) (z : G)
    (hzX : z ∈ X) (hzc : z ∈ Subgroup.centralizer (X : Set G)) (hz1 : z ≠ 1) (hzp : z ^ p = 1) :
    GGResXDatumAx p Bs X z lab.rank ∨
      (p ^ 2 ∣ Nat.gcd (lab.rank + 1) (ggTorM lab) ∧ GGResXDatumA p Bs X lab.rank) := by
  have hp : p.Prime := Fact.out
  have hrow := GGTBTorRowAt.aDep htag h4 hdvd hM hex
  obtain ⟨hodd, hpm, hMw, hMC⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  obtain ⟨hN, hTor⟩ := ggTorData_of_hasLabel hRig hInn hTB hlab hhas
    (ggTBTorWRows_of_all hT p lab _ _ _ _ _ hp hp2 hlab hrow)
    (hLift p lab _ _ _ _ _ hp hp2 hlab hrow)
  obtain ⟨w, hw⟩ := hTor
  have hcore := ggResXDatumA_ind_of_wit hp2 hodd hpm hMw hMC hBs hS hN w hw
  by_cases hp2n : p ^ 2 ∣ Nat.gcd (lab.rank + 1) (ggTorM lab)
  · exact Or.inr ⟨hp2n, hcore.1⟩
  · refine Or.inl (hcore.2 ?_ z)
    obtain ⟨hzcen, hzo⟩ := ggTI_central hzX hzc hz1 hzp
    have hxs := ggTor_central_mem_closure_A hp hp2 hodd hpm (by omega) hdvd hp2n w hw
      hw.2.2.2.2.2.1 _ hzcen hzo
    exact w.coroot_indep_of_center hp hodd hpm hw ggCartanA_ker_le_one _ hzcen hzo hxs

theorem ggTwoNodeIndepE6_of_tbTor (hRig : GGLabelRigidInput) (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hp3 : p = 3) (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hInn : GGInnerDiagOn Bs X) (hTB : GGTorusTBAt p Bs X) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X))
    (htag : lab.tag = .E6) (hM : 3 ∣ ggTorM lab) (z : G) (hzX : z ∈ X)
    (hzc : z ∈ Subgroup.centralizer (X : Set G)) (hz1 : z ≠ 1) (hzp : z ^ p = 1) :
    GGResXDatumE6x p Bs X z := by
  subst hp3
  have hp : Nat.Prime 3 := Fact.out
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hrow := GGTBTorRowAt.e6Three htag rfl hM
  obtain ⟨hodd, hpm, hMw, hMC⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  obtain ⟨hN, hTor⟩ := ggTorData_of_hasLabel hRig hInn hTB hlab hhas
    (ggTBTorWRows_of_all hT 3 lab _ _ _ _ _ hp hp2 hlab hrow)
    (hLift 3 lab _ _ _ _ _ hp hp2 hlab hrow)
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨hzcen, hzo⟩ := ggTI_central hzX hzc hz1 hzp
  have hxs := ggTor_central_mem_closure_E6 hodd hpm w hw hw.2.2.2.2.2.1 _ hzcen hzo
  exact ggResXDatumE6x_of_wit hp2 hodd hpm hMw hMC hBs hS hN w hw
    (w.coroot_indep_of_center hp hodd hpm hw ggCartanE₆_ker_le_one _ hzcen hzo hxs) z

theorem ggTwoNodeIndepDatum_of_tbTor (hRig : GGLabelRigidInput) (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hLoc : GGE6D4TwoNodeLocalInput) (hEn : GGTwoNodeIndepTwA5RowInput) :
    GGTwoNodeIndepDatum := by
  intro G _ _ p B Bs x L D J y K hH hfact X z hXz labJ labX hJΛ hXΛ hJl hXl hrow hzX
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hrow0 := hrow
  have hdata : z ∈ Subgroup.centralizer (X : Set G) ∧ z ≠ 1 ∧ z ^ p = 1 ∧
      GGInnerDiagOn Bs X ∧ GGTorusTBAt p Bs X := by
    rcases hXz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨hc, h1, hpz, hperf⟩ := GGConfig.data_L hH.1
      exact ⟨hc, h1, hpz, hH.2.2.1.1, ggTorusTBAt_L hH.1 hperf⟩
    · obtain ⟨hc, h1, hpz, hperf⟩ := hH.data_K
      exact ⟨hc, h1, hpz, hH.2.2.1.2 _ _ hH.2.2.2.2.1,
        ggTorusTBAt_nbr hH.1 hH.2.2.2.2.1 hperf⟩
  obtain ⟨hzc, hz1, hzp, hInn, hTB⟩ := hdata
  have hJrankA : labJ.tag = .A → 1 ≤ labJ.rank := fun ht => by
    have h2 := hJΛ.2
    rw [ht] at h2
    exact h2.1
  have hJrankT : labJ.tag = .twA → 1 ≤ labJ.rank := fun ht => by
    have h2 := hJΛ.2
    rw [ht] at h2
    have h3 := h2.1
    omega
  rcases hrow with ⟨hJt, hJd, hJr, hXe⟩ | ⟨hJt, hJd, hJr, hXe⟩ | ⟨hJe, hp3, hd, hXe⟩ |
    ⟨hJe, hp3, hd, hXe⟩
  ·
    have hXt : labX.tag = .A := by rw [hXe]
    have hXr : labX.rank = labJ.rank + 2 := by rw [hXe]
    have hXn : labX.n = labJ.n := by rw [hXe]
    have h4 : 4 ≤ labX.rank := by
      rw [hXr]
      exact ggTI_four_le hp hp2 (hJrankA hJt) hJr
    have hdvd : p ∣ labX.rank + 1 := by
      rw [hXr]
      simpa [add_assoc] using hJr
    have hM : p ∣ ggTorM labX := by
      unfold ggTorM
      rw [if_neg (by simp [hXt]), hXn]
      exact hJd
    have hex : ¬ (p = 3 ∧ labX.rank = 5 ∧ p ∣ 2 ^ labX.n + 1) := by
      rintro ⟨-, -, h⟩
      rw [hXn] at h
      have h1 : 1 ≤ 2 ^ labJ.n := Nat.one_le_two_pow
      have h2 : 2 ^ labJ.n + 1 = (2 ^ labJ.n - 1) + 2 := by omega
      rw [h2] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((Nat.dvd_add_right hJd).mp h))
    exact Or.inl ⟨Or.inl hXt, ggTwoNodeIndepA_of_tbTor hRig hT hLift hp2 hBs hS hInn hTB hXΛ hXl
      (Or.inl hXt) h4 hdvd hM hex z hzX hzc hz1 hzp⟩
  ·
    have hXt : labX.tag = .twA := by rw [hXe]
    have hXr : labX.rank = labJ.rank + 2 := by rw [hXe]
    have hXn : labX.n = labJ.n := by rw [hXe]
    have h4 : 4 ≤ labX.rank := by
      rw [hXr]
      exact ggTI_four_le hp hp2 (hJrankT hJt) hJr
    have hdvd : p ∣ labX.rank + 1 := by
      rw [hXr]
      simpa [add_assoc] using hJr
    have hM : p ∣ ggTorM labX := by
      unfold ggTorM
      rw [if_pos (by simp [hXt]), hXn]
      exact hJd
    by_cases hex : p = 3 ∧ labX.rank = 5 ∧ p ∣ 2 ^ labX.n + 1
    · obtain ⟨hp3, hr5, hd3⟩ := hex
      subst hp3
      have h1 := hEn G 3 B Bs x L D J y K hH X z hXz labJ labX hJΛ hXΛ hJl hXl hrow0 hzX rfl
        ⟨hXt, hr5, hd3⟩
      rw [← hr5] at h1
      exact Or.inl ⟨Or.inr hXt, Or.inl h1⟩
    · exact Or.inl ⟨Or.inr hXt, ggTwoNodeIndepA_of_tbTor hRig hT hLift hp2 hBs hS hInn hTB hXΛ
        hXl (Or.inr hXt) h4 hdvd hM hex z hzX hzc hz1 hzp⟩
  ·
    have hXt : labX.tag = .E6 := by rw [hXe]
    have hXn : labX.n = labJ.n := by rw [hXe]
    have hM : 3 ∣ ggTorM labX := by
      unfold ggTorM
      rw [if_neg (by simp [hXt]), hXn]
      exact hd
    exact Or.inr ⟨Or.inl hXt, ggTwoNodeIndepE6_of_tbTor hRig hT hLift hp3 hBs hS hInn hTB hXΛ hXl
      hXt hM z hzX hzc hz1 hzp⟩
  ·
    have hXt : labX.tag = .twE6 := by rw [hXe]
    subst hp3
    exact Or.inr ⟨Or.inr hXt, (hLoc G B Bs x L D J y K hH X z hXz labJ labX hJΛ hXΛ hJl hXl hrow0
      (Or.inr hXt)).2.2.2.1⟩

end CFSG.StandardType
