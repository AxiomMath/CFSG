module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSCLiftP

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem lift_conj_mem_of_mem_normalizer {p : ℕ} (hp : p.Prime) {M R : Type} [Group M]
    [Finite M] [Group R] {L' E : Subgroup M} {θ : L' ⧸ Subgroup.center L' ≃* R}
    (hcp : GGCenterPrime p R) (hEA : IsElemAbelian p E) (hL : commutator L' = ⊤) {ρ : E →* R}
    (hρψ : ∀ (e : E) (he : (e : M) ∈ L'), ρ e = ggQuotHom θ ⟨(e : M), he⟩)
    {lam : E →* L'} (hlamψ : ∀ e, ggQuotHom θ (lam e) = ρ e) (hlamp : ∀ e, lam e ^ p = 1)
    (hlamE : ∀ e, ((lam e : L') : M) ∈ E)
    (hdec : ∀ x ∈ E, ∃ a ∈ E ⊓ L', ∃ z ∈ E ⊓ Subgroup.centralizer (L' : Set M), x = a * z)
    {n : L'} (hn : ggQuotHom θ n ∈ Subgroup.normalizer (ρ.range : Set R)) {x : M}
    (hx : x ∈ E) : (n : M) * x * (n : M)⁻¹ ∈ E := by
  obtain ⟨a, ⟨haE, haL⟩, z, ⟨hzE, hzC⟩, rfl⟩ := hdec x hx
  have hmem : ggQuotHom θ (n * ⟨a, haL⟩ * n⁻¹) ∈ ρ.range := by
    have h := (Subgroup.mem_normalizer_iff.mp hn (ρ ⟨a, haE⟩)).mp ⟨⟨a, haE⟩, rfl⟩
    rwa [hρψ ⟨a, haE⟩ haL, ← map_inv, ← map_mul, ← map_mul] at h
  obtain ⟨e, he⟩ := hmem
  have hpow : (n * ⟨a, haL⟩ * n⁻¹) ^ p = 1 := by
    rw [conj_pow, show (⟨a, haL⟩ : L') ^ p = 1 from Subtype.ext (hEA.2 a haE), mul_one,
      mul_inv_cancel]
  have hlam := congrArg Subtype.val
    (TorusSCLift.eq_lambda_of_lift hp hcp hL hlamψ hlamp e he.symm hpow)
  have hz : (n : M) * z * (n : M)⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hzC n n.2]
    group
  rw [show (n : M) * (a * z) * (n : M)⁻¹ = (n : M) * a * (n : M)⁻¹ * ((n : M) * z * (n : M)⁻¹)
    by group, hz]
  refine E.mul_mem ?_ hzE
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at hlam
  rw [hlam]
  exact hlamE e

private theorem mem_normalizer_of_mem_normalizer {p : ℕ} (hp : p.Prime) {M R : Type} [Group M]
    [Finite M] [Group R] {L' E : Subgroup M} {θ : L' ⧸ Subgroup.center L' ≃* R}
    (hcp : GGCenterPrime p R) (hEA : IsElemAbelian p E) (hL : commutator L' = ⊤) {ρ : E →* R}
    (hρψ : ∀ (e : E) (he : (e : M) ∈ L'), ρ e = ggQuotHom θ ⟨(e : M), he⟩)
    {lam : E →* L'} (hlamψ : ∀ e, ggQuotHom θ (lam e) = ρ e) (hlamp : ∀ e, lam e ^ p = 1)
    (hlamE : ∀ e, ((lam e : L') : M) ∈ E)
    (hdec : ∀ x ∈ E, ∃ a ∈ E ⊓ L', ∃ z ∈ E ⊓ Subgroup.centralizer (L' : Set M), x = a * z)
    {n : L'} (hn : ggQuotHom θ n ∈ Subgroup.normalizer (ρ.range : Set R)) :
    (n : M) ∈ Subgroup.normalizer (E : Set M) := by
  have hn' : ggQuotHom θ n⁻¹ ∈ Subgroup.normalizer (ρ.range : Set R) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hn
  refine Subgroup.mem_normalizer_iff.mpr fun x =>
    ⟨lift_conj_mem_of_mem_normalizer hp hcp hEA hL hρψ hlamψ hlamp hlamE hdec hn, fun hx => ?_⟩
  have h := lift_conj_mem_of_mem_normalizer hp hcp hEA hL hρψ hlamψ hlamp hlamE hdec hn' hx
  simpa [mul_assoc] using h

private theorem mem_centralizer_of_mem_center {p : ℕ} (hp : p.Prime) {M : Type} [Group M]
    {L' E : Subgroup M} (hcpZ : ¬ p ∣ Nat.card (Subgroup.center L')) :
    ∀ z ∈ L' ⊓ Subgroup.centralizer (L' : Set M), z ^ p = 1 →
      z ∈ Subgroup.centralizer (E : Set M) := by
  intro z hz hzp
  obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
  have hz1 : (⟨z, hzL⟩ : L') = 1 :=
    TorusSCLift.eq_one_of_mem_center_of_pow hp hcpZ
      (Subgroup.mem_center_iff.mpr fun l => Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC l l.2))
      ⟨1, Subtype.ext (by simpa using hzp)⟩
  rw [show z = 1 from congrArg Subtype.val hz1]
  exact Subgroup.one_mem _

private theorem quotHom_mem_centralizer {M R : Type} [Group M] [Group R] {L' E E₁ : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)} {ρ : E →* R}
    (hρ : ∀ e : E, MulAut.conj (ρ e) = ggLAut L' θ ⟨e, hE e.2⟩)
    (hρrange : (E₁.subgroupOf E).map ρ = ρ.range) {c : M} (hcL : c ∈ L')
    (hcC : c ∈ Subgroup.centralizer (E₁ : Set M)) :
    ggQuotHom θ ⟨c, hcL⟩ ∈ Subgroup.centralizer (ρ.range : Set R) := by
  rw [← hρrange, Subgroup.mem_centralizer_iff]
  rintro _ ⟨e, he, rfl⟩
  have hec : (e : M) * c * (e : M)⁻¹ = c := by
    rw [Subgroup.mem_centralizer_iff.mp hcC e (Subgroup.mem_subgroupOf.mp he)]
    group
  have hmem : (e : M) * c * (e : M)⁻¹ ∈ L' := by
    rw [hec]
    exact hcL
  have h := L45KG.ggQuotHom_conj (K := L') (θ := θ) (hE e.2) hcL hmem
  rw [show (⟨(e : M) * c * (e : M)⁻¹, hmem⟩ : L') = ⟨c, hcL⟩ from Subtype.ext hec, ← hρ e,
    MulAut.conj_apply] at h
  calc ρ e * ggQuotHom θ ⟨c, hcL⟩
      = ρ e * ggQuotHom θ ⟨c, hcL⟩ * (ρ e)⁻¹ * ρ e := by group
    _ = ggQuotHom θ ⟨c, hcL⟩ * ρ e := by rw [← h]

private theorem closure_conj_le_map {M R : Type} [Group M] [Group R] {L' : Subgroup M}
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (S : Subgroup L') (Wbar : Set R) :
    Subgroup.closure (⋃ n ∈ Wbar, (fun s => n * s * n⁻¹) '' (S.map ψ : Set R)) ≤
      ((Subgroup.closure (⋃ n ∈ {n : M | ∃ hn : n ∈ L', ψ ⟨n, hn⟩ ∈ Wbar},
        (fun s => n * s * n⁻¹) '' (S.map L'.subtype : Set M))).subgroupOf L').map ψ := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image] at hx
  obtain ⟨nbar, hnbar, _, ⟨s, hs, rfl⟩, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hψ nbar
  refine ⟨n * s * n⁻¹, Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ?_), ?_⟩
  · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
    exact ⟨n, ⟨n.2, hnbar⟩, s, ⟨s, hs, rfl⟩, rfl⟩
  · simp only [map_mul, map_inv]

private theorem mem_of_map_mem {p : ℕ} (hp : p.Prime) {L R : Type} [Group L] [Group R]
    {ψ : L →* R} (hker : ψ.ker ≤ Subgroup.center L) (hpker : ¬ p ∣ Nat.card ψ.ker)
    {H : Subgroup L} {c : L} (hc : ψ c ∈ H.map ψ) (hcp : ∃ k : ℕ, c ^ p ^ k = 1) : c ∈ H := by
  obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.mp hc
  obtain ⟨k, hk⟩ := hcp
  have hz : c * x⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxc, mul_inv_cancel]
  have hm : (c * x⁻¹) ^ Nat.card ψ.ker = 1 := by
    have h : (⟨c * x⁻¹, hz⟩ : ψ.ker) ^ Nat.card ψ.ker = 1 := pow_card_eq_one'
    simpa using congrArg Subtype.val h
  have hcm : c ^ Nat.card ψ.ker ∈ H := by
    have hcomm : Commute (c * x⁻¹) x := (Subgroup.mem_center_iff.mp (hker hz) x).symm
    rw [show c = c * x⁻¹ * x by group, hcomm.mul_pow, hm, one_mul]
    exact H.pow_mem hx _
  have hcop : (Nat.card ψ.ker).Coprime (orderOf c) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
      (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpker).symm.pow_right k)
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← ht]
  exact H.pow_mem hcm t

private theorem exists_gen_of_torusGenR {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)}
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R) (hgen : GGTorusGenR p r R)
    {M : Type} [Group M] [Finite M] {L' E E₁ D' J' : Subgroup M} {d : M}
    {θ : L' ⧸ Subgroup.center L' ≃* R} {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E I θ hE) (hr : p ^ (r + 1) ≤ Nat.card E)
    (hne : E ⊓ Subgroup.centralizer (L' : Set M) ≠ ⊥) (hE₁ : E₁ ≤ E)
    (hbot : E₁ ⊓ Subgroup.centralizer (L' : Set M) = ⊥) (hcard : Nat.card E = p * Nat.card E₁)
    (hnorm : Subgroup.normalizer (E : Set M) ≤ Subgroup.normalizer (E₁ : Set M))
    (hD'E : D' ≤ E) (hDE : E ⊓ Subgroup.centralizer (L' : Set M) ≤ D')
    (hD'd : D' ⊓ E₁ = Subgroup.zpowers d) (hd : d ≠ 1)
    (hJ : IsComponentOf J' (L' ⊓ Subgroup.centralizer (D' : Set M))) {c : M}
    (hc : c ∈ L' ⊓ Subgroup.centralizer (E₁ : Set M)) (hcpow : ∃ k : ℕ, c ^ p ^ k = 1) :
    ∃ (S : Subgroup M) (W : Set M), IsPGroup p S ∧ S ≤ Subgroup.centralizer (E₁ : Set M) ∧
      S ≤ J' ∧ W ⊆ Subgroup.normalizer (E₁ : Set M) ∧
      c ∈ Subgroup.closure (⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set M)) := by
  obtain ⟨hcL, hcC⟩ := Subgroup.mem_inf.mp hc
  have hkerψ := ker_ggQuotHom θ
  have hcpZ := TorusSCLift.center_not_dvd θ hcp hpos.1
  obtain ⟨ρ, hρ, hρker, hρψ⟩ := TorusSCLift.exists_rho hpos.2.1 hpos.2.2.2.1 hI hZ hpos.1
  obtain ⟨lam, hlamψ, hlamp⟩ := TorusSCLift.exists_lambda (θ := θ) hp hpos.2.1 hcp hpos.1 ρ
  have hlamE := TorusSCLift.lambda_mem hp hpos hcp hρ hlamψ hlamp
  obtain ⟨-, hρbig, hρrange⟩ :=
    TorusSCLift.card_range_rho (p := p) (r := r) hp hpos hr hne hE₁ hbot hcard hρker
  have hdec := TorusSCLift.decomp_inf_centralizer hρker hρψ hlamψ hlamE
  have hdD : d ∈ D' ⊓ E₁ := hD'd ▸ Subgroup.mem_zpowers d
  have hdE : d ∈ E := hD'E hdD.1
  have hρd : ρ ⟨d, hdE⟩ ≠ 1 := fun h1 => hd (Subgroup.mem_bot.mp
    (hbot ▸ Subgroup.mem_inf.mpr ⟨hdD.2, (hρker ⟨d, hdE⟩).mp h1⟩))
  have hĒA : IsElemAbelian p ρ.range := by
    have htop : IsElemAbelian p (⊤ : Subgroup E) :=
      ⟨⟨⟨fun a b => Subtype.ext (hpos.2.1.1.is_comm.comm a b)⟩⟩,
        fun x _ => Subtype.ext (hpos.2.1.2 x x.2)⟩
    rw [MonoidHom.range_eq_map]
    exact isElemAbelian_map htop ρ
  obtain ⟨k, hk⟩ := hcpow
  have hck : (⟨c, hcL⟩ : L') ^ p ^ k = 1 := Subtype.ext (by simpa using hk)
  obtain ⟨Sbar, Wbar, hSp, hSC, hSJ, hWN, hcgen⟩ := hgen ρ.range hĒA hρbig
    (TorusSCLift.image_self_centralizing hp hpos hcp hρ hρψ) (ρ ⟨d, hdE⟩) ⟨⟨d, hdE⟩, rfl⟩ hρd _
    (TorusSCLift.component_image hpos hdE
      (exists_mul_of_complement_position hp hpos hne hE₁ hbot hcard).1 hD'E hDE hD'd hJ hρ)
    (ggQuotHom θ ⟨c, hcL⟩) (quotHom_mem_centralizer hρ hρrange hcL hcC)
    ⟨k, by rw [← map_pow, hck, map_one]⟩
  obtain ⟨SL, hSLp, hSLJ, rfl⟩ :=
    TorusSCLift.exists_lift_isPGroup_subgroup hp (hkerψ ▸ hcpZ) hSp hSJ
  refine ⟨SL.map L'.subtype, {n | ∃ hn : n ∈ L', ggQuotHom θ ⟨n, hn⟩ ∈ Wbar}, hSLp.map _,
    TorusSCLift.map_le_centralizer_of_mem_range hp hE₁ hdec hcpZ hρψ hSLp
      fun s hs => hSC ⟨s, hs, rfl⟩, ?_, fun n ⟨hnL, hnW⟩ => hnorm ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hSLJ hs)
  · exact mem_normalizer_of_mem_normalizer (n := ⟨n, hnL⟩) hp hcp hpos.2.1 hpos.1 hρψ hlamψ hlamp
      hlamE hdec (hWN hnW)
  · exact Subgroup.mem_subgroupOf.mp (mem_of_map_mem hp hkerψ.le (hkerψ ▸ hcpZ)
      (closure_conj_le_map (ggQuotHom_surjective θ) SL Wbar hcgen) ⟨k, hck⟩)

theorem ggTorusGenTableBRk_of_torusGenR {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)}
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R) (hgen : GGTorusGenR p r R) :
    GGTorusGenTableBRk p R I (r + 1) := by
  intro M _ _ L' E E₁ D' J' d θ hE hpos hr hne hE₁ hbot hcard hnorm hD'E hDE hD'd hd hJ
  exact ⟨mem_centralizer_of_mem_center hp (TorusSCLift.center_not_dvd θ hcp hpos.1),
    fun c hc hcpow _ => exists_gen_of_torusGenR hp hI hZ hcp hgen hpos hr hne hE₁ hbot hcard
      hnorm hD'E hDE hD'd hd hJ hc hcpow⟩

theorem ggTorusGenTableB_of_torusGenR {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)}
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R) (hgen : GGTorusGenR p 3 R) :
    GGTorusGenTableB p R I := by
  intro M _ _ L' E E₁ D' J' d θ hE hpos
  exact ggTorusGenTableBRk_of_torusGenR hp hI hZ hcp hgen M L' E E₁ D' J' d θ hE hpos
    hpos.2.2.1

private theorem mem_map_of_comm_pow {p : ℕ} {R R' : Type*} [Group R] [Group R'] (e : R ≃* R')
    {E : Subgroup R}
    (hsc : ∀ g : R, (∀ y ∈ E, g * y = y * g) → g ^ p = 1 → g ∈ E) :
    ∀ g : R', (∀ y ∈ E.map e.toMonoidHom, g * y = y * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
  intro g hg hgp
  obtain ⟨y, rfl⟩ := e.surjective g
  change e.toMonoidHom y ∈ Subgroup.map e.toMonoidHom E
  rw [Subgroup.mem_map_iff_mem (K := E) (x := y) e.injective]
  refine hsc y (fun x hx => ?_) ?_
  · apply e.injective
    rw [map_mul, map_mul]
    exact hg (e.toMonoidHom x)
      ((Subgroup.mem_map_iff_mem (K := E) (x := x) e.injective).mpr hx)
  · apply e.injective
    rw [map_pow, map_one]
    exact hgp

private theorem map_centralizer_le_centralizer_image_equiv {R R' : Type*} [Group R] [Group R']
    (e : R ≃* R') (E : Subgroup R) :
    (Subgroup.centralizer ((E.map e.toMonoidHom : Subgroup R') : Set R')).map
        e.symm.toMonoidHom ≤ Subgroup.centralizer (E : Set R) := by
  have hset : e.symm.toMonoidHom '' (E.map e.toMonoidHom : Set R') = (E : Set R) := by
    rw [← Subgroup.coe_map, Subgroup.map_map]
    simp
  simpa only [hset] using Subgroup.map_centralizer_le_centralizer_image
    (E.map e.toMonoidHom : Set R') e.symm.toMonoidHom

private theorem map_normalizer_image_equiv {R R' : Type*} [Group R] [Group R'] (e : R ≃* R')
    (E : Subgroup R) :
    (Subgroup.normalizer ((E.map e.toMonoidHom : Subgroup R') : Set R')).map
        e.symm.toMonoidHom = Subgroup.normalizer (E : Set R) := by
  rw [Subgroup.map_equiv_normalizer_eq, Subgroup.map_map]
  simp

private theorem map_iUnion_conj_image {R R' : Type*} [Group R] [Group R'] (e : R ≃* R')
    (S : Subgroup R) (W' : Set R') :
    e.toMonoidHom '' (⋃ n ∈ e.symm '' W',
        (fun s => n * s * n⁻¹) '' (S : Set R)) =
      ⋃ n ∈ W', (fun s => n * s * n⁻¹) '' ((S.map e.toMonoidHom : Subgroup R') : Set R') := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨n, hnW, hz'⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨n', hn', hnn'⟩ := (Set.mem_image e.symm W' n).mp hnW
    obtain ⟨s, hsS, hzs⟩ := (Set.mem_image (fun s => n * s * n⁻¹) (S : Set R) z).mp hz'
    have hval : e.toMonoidHom z = n' * e.toMonoidHom s * n'⁻¹ := by
      rw [← hzs, ← hnn']
      simp [map_mul]
    rw [hval]
    refine Set.mem_iUnion₂.mpr ⟨n', hn', ?_⟩
    exact Set.mem_image_of_mem (fun t => n' * t * n'⁻¹)
      (Subgroup.mem_map_of_mem e.toMonoidHom hsS)
  · intro hy
    obtain ⟨n', hn', hy'⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨y', hy'mem, hyy'⟩ :=
      (Set.mem_image (fun s => n' * s * n'⁻¹) (S.map e.toMonoidHom : Set R') y).mp hy'
    obtain ⟨s, hsS, hys⟩ := Subgroup.mem_map.mp hy'mem
    have hval : e.toMonoidHom (e.symm n' * s * (e.symm n')⁻¹) =
        n' * e.toMonoidHom s * n'⁻¹ := by
      simp [map_mul]
    rw [← hys] at hyy'
    rw [← hval] at hyy'
    rw [← hyy']
    refine Set.mem_image_of_mem e.toMonoidHom ?_
    refine Set.mem_iUnion₂.mpr ⟨e.symm n', ?_, ?_⟩
    · exact Set.mem_image_of_mem e.symm hn'
    · exact Set.mem_image_of_mem (fun s => e.symm n' * s * (e.symm n')⁻¹) hsS

theorem ggTorusGenR_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGTorusGenR p r R') : GGTorusGenR p r R := by
  intro E hE hcard hsc x hx hx1 J hJ c hc hcp
  have hE' : IsElemAbelian p (E.map e.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE e.toMonoidHom
  have hcard' : p ^ r ≤ Nat.card (E.map e.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  have hx' : e x ∈ E.map e.toMonoidHom := ⟨x, hx, rfl⟩
  have hx1' : e x ≠ 1 := fun h1 => hx1 (e.map_eq_one_iff.mp h1)
  have hJ' : IsComponentOf (J.map e.toMonoidHom)
      (Subgroup.centralizer ({e x} : Set R')) := by
    rw [← TableBSymp.map_centralizer_singleton e x]
    exact isComponentOf_map_mulEquiv' e hJ
  have hc' : e c ∈ Subgroup.centralizer (E.map e.toMonoidHom : Set R') := by
    change e.toMonoidHom c ∈ Subgroup.centralizer (E.map e.toMonoidHom : Set R')
    exact Subgroup.map_centralizer_le_centralizer_image (E : Set R) e.toMonoidHom
      (Subgroup.mem_map_of_mem e.toMonoidHom hc)
  have hcp' : ∃ k : ℕ, (e c) ^ p ^ k = 1 := by
    obtain ⟨k, hk⟩ := hcp
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨S', W', hS'p, hS'cent, hS'J, hW'nrm, hcgen⟩ :=
    h (E.map e.toMonoidHom) hE' hcard' (mem_map_of_comm_pow e hsc) (e x) hx' hx1'
      (J.map e.toMonoidHom) hJ' (e c) hc' hcp'
  let S : Subgroup R := S'.map e.symm.toMonoidHom
  let W : Set R := e.symm '' W'
  let U : Set R := ⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set R)
  let T : Set R' := ⋃ n ∈ W', (fun s => n * s * n⁻¹) '' (S' : Set R')
  have hSmap : S.map e.toMonoidHom = S' := by
    rw [show S = S'.map e.symm.toMonoidHom from rfl, Subgroup.map_map]
    simp
  have himg : e.toMonoidHom '' U = T := by
    change e.toMonoidHom '' (⋃ n ∈ e.symm '' W',
      (fun s => n * s * n⁻¹) '' (S : Set R)) =
      ⋃ n ∈ W', (fun s => n * s * n⁻¹) '' (S' : Set R')
    simpa only [hSmap] using map_iUnion_conj_image e S W'
  refine ⟨S, W, ?_, ?_, ?_, ?_, ?_⟩
  · show IsPGroup p (S'.map e.symm.toMonoidHom)
    exact hS'p.map e.symm.toMonoidHom
  · exact (Subgroup.map_mono hS'cent).trans (map_centralizer_le_centralizer_image_equiv e E)
  · have hJ' : S' ≤ J.comap e.symm.toMonoidHom := by
      rwa [Subgroup.map_equiv_eq_comap_symm'] at hS'J
    exact (Subgroup.map_le_iff_le_comap (f := e.symm.toMonoidHom)).mpr hJ'
  · rintro n ⟨n', hn', rfl⟩
    change e.symm n' ∈ Subgroup.normalizer (E : Set R)
    exact (map_normalizer_image_equiv e E) ▸
      Subgroup.mem_map_of_mem e.symm.toMonoidHom (hW'nrm hn')
  · change c ∈ Subgroup.closure U
    have hmap : (Subgroup.closure U).map e.toMonoidHom = Subgroup.closure T := by
      rw [MonoidHom.map_closure, himg]
    have hc'' : e c ∈ (Subgroup.closure U).map e.toMonoidHom := by
      rw [hmap]
      exact hcgen
    exact (Subgroup.mem_map_iff_mem (K := Subgroup.closure U) (x := c) e.injective).mp hc''

end CFSG.StandardType
