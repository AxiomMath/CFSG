module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Flag
public import CFSG.Quasithin.Vol2.Ch11G2Q8Comm
public import CFSG.Quasithin.Vol2.KGNatSL3Flag

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem g2Act_mul_apply (a b : ↥(cayleyGroup K)) (x : Ix3 → K) :
    g2Act (a * b) x = g2Act a (g2Act b x) := by
  rw [map_mul]
  rfl

theorem g2Act_inv_apply (g : ↥(cayleyGroup K)) (x : Ix3 → K) : g2Act g⁻¹ (g2Act g x) = x := by
  rw [← g2Act_mul_apply, inv_mul_cancel, map_one]
  rfl

theorem g2Act_apply_inv (g : ↥(cayleyGroup K)) (x : Ix3 → K) : g2Act g (g2Act g⁻¹ x) = x := by
  rw [← g2Act_mul_apply, mul_inv_cancel, map_one]
  rfl

theorem g2Derived_eq {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K := by
  rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
    cayley_commutator_eq hc0 hc1]

theorem g2Derived_le : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ cayleyGroup K := by
  rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
  exact Subgroup.commutator_le_self _

noncomputable abbrev lmG (K : Type) [Field K] [CharP K 2] :
    LinModel (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) K (Ix3 → K) :=
  linModelZorn _ g2Derived_le

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

@[expose] noncomputable def rhoG {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H) : ↥(cayleyGroup K) →* ↥H :=
  π.comp (MulEquiv.subgroupCongr (g2Derived_eq hc0 hc1).symm).toMonoidHom

theorem IsCoord.actG (hf : IsCoord (lmG K) H Z π f) {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (g : ↥(cayleyGroup K)) (w : W) :
    f (((rhoG hc0 hc1 π g : ↥H) : MulAut W) w) = g2Act g (f w) :=
  (hf.act _ w).trans (linModelZorn_lin _ _ _ _)

theorem rhoG_bijective (hf : IsCoord (lmG K) H Z π f) {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    Function.Bijective (rhoG hc0 hc1 π) := by
  refine ⟨fun g g' h => ?_, hf.onto.comp (MulEquiv.subgroupCongr _).surjective⟩
  have hlin : ∀ x, g2Act g x = g2Act g' x := by
    intro x
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [← IsCoord.actG hf hc0 hc1, ← IsCoord.actG hf hc0 hc1, h]
  have h1 : g⁻¹ * g' = 1 := cayley_eq_one fun x => by
    rw [g2Act_mul_apply, ← hlin, g2Act_inv_apply]
  exact (inv_mul_eq_one.mp h1)

theorem not_two_dvd_index_U0 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    ¬ 2 ∣ (U0 K).index := by
  have := finite_cayleyGroup (F := K)
  have h := (U0 K).card_mul_index
  rw [card_U0 hK, card_cayleyGroup] at h
  have hq : 0 < Nat.card K ^ 6 := by rw [hK]; positivity
  have hidx : (U0 K).index = (Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1) :=
    Nat.eq_of_mul_eq_mul_left hq h
  rw [hidx]
  have he : Even (Nat.card K) := by
    rw [hK]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have h1 : 1 ≤ Nat.card K ^ 6 := Nat.one_le_pow _ _ (by rw [hK]; positivity)
  have h2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by rw [hK]; positivity)
  have hodd : Odd ((Nat.card K ^ 6 - 1) * (Nat.card K ^ 2 - 1)) := Nat.odd_mul.mpr
    ⟨Nat.Even.sub_odd h1 (Nat.even_pow.mpr ⟨he, by norm_num⟩) odd_one,
      Nat.Even.sub_odd h2 (Nat.even_pow.mpr ⟨he, by norm_num⟩) odd_one⟩
  exact fun h2' => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2')

theorem exists_sylow_eq_conj_U0 [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (hf : IsCoord (lmG K) H Z π f) {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    {P : Subgroup (MulAut W)} (hP : CFSG.QuasithinUnique.IsSylowTwoOf P H) :
    ∃ g : ↥(cayleyGroup K), ∀ x : MulAut W,
      x ∈ P ↔ ∃ u ∈ U0 K, x = ((rhoG hc0 hc1 π (g * u * g⁻¹) : ↥H) : MulAut W) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_cayleyGroup (F := K)
  obtain ⟨hPH, hP2, hPi⟩ := hP
  obtain ⟨hinj, hsurj⟩ := rhoG_bijective hf hc0 hc1
  have hQ2 := isPGroup_comap (rhoG hc0 hc1 π) hinj hP2
  have hQi : ¬ 2 ∣ ((P.subgroupOf H).comap (rhoG hc0 hc1 π)).index := by
    rw [index_comap (rhoG hc0 hc1 π) hsurj]
    exact hPi
  obtain ⟨g, hg⟩ := CFSG.CGT.Timmesfeld75.exists_conjSubgroup_eq_of_sylow
    (IsPGroup.toSylow isPGroup_U0 (not_two_dvd_index_U0 hK hn)) (hQ2.toSylow hQi)
  refine ⟨g, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨A, hA⟩ := hsurj ⟨x, hPH hx⟩
    have hAQ : A ∈ (P.subgroupOf H).comap (rhoG hc0 hc1 π) := by
      rw [Subgroup.mem_comap, hA, Subgroup.mem_subgroupOf]
      exact hx
    rw [← IsPGroup.toSylow_coe hQ2 hQi, ← hg, CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hAQ
    refine ⟨g⁻¹ * A * g, hAQ, ?_⟩
    rw [show g * (g⁻¹ * A * g) * g⁻¹ = A by group, hA]
  · rintro ⟨u, hu, rfl⟩
    have hmem : g * u * g⁻¹ ∈ (P.subgroupOf H).comap (rhoG hc0 hc1 π) := by
      rw [← IsPGroup.toSylow_coe hQ2 hQi, ← hg, CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      rwa [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hmem
    exact hmem

end Real

@[expose] noncomputable def gmapG (g : ↥(cayleyGroup K)) (S : Submodule K (Ix3 → K)) :
    Submodule K (Ix3 → K) :=
  S.map (zornLin (g : quasithinZorn K ≃ₗ[K] quasithinZorn K))

theorem zornLin_apply_eq (g : ↥(cayleyGroup K)) (x : Ix3 → K) :
    zornLin (g : quasithinZorn K ≃ₗ[K] quasithinZorn K) x = g2Act g x := rfl

theorem mem_gmapG {g : ↥(cayleyGroup K)} {S : Submodule K (Ix3 → K)} {x : Ix3 → K} :
    x ∈ gmapG g S ↔ g2Act g⁻¹ x ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [zornLin_apply_eq, g2Act_inv_apply]
    exact hy
  · intro hx
    exact ⟨_, hx, by rw [zornLin_apply_eq, g2Act_apply_inv]⟩

theorem card_gmapG (g : ↥(cayleyGroup K)) (S : Submodule K (Ix3 → K)) :
    Nat.card (gmapG g S) = Nat.card S := by
  have hinj : Function.Injective (zornLin (g : quasithinZorn K ≃ₗ[K] quasithinZorn K)) := by
    intro x y h
    rw [zornLin_apply_eq, zornLin_apply_eq] at h
    rw [← g2Act_inv_apply g x, h, g2Act_inv_apply]
  exact Nat.card_congr (Submodule.equivMapOfInjective _ hinj S).toEquiv.symm

theorem gmapG_gmapG_inv (g : ↥(cayleyGroup K)) (S : Submodule K (Ix3 → K)) :
    gmapG g (gmapG g⁻¹ S) = S := by
  ext x
  rw [mem_gmapG, mem_gmapG, inv_inv, g2Act_apply_inv]

theorem U0Stable.mem_iff {S : Submodule K (Ix3 → K)} (hS : U0Stable S) {u : ↥(cayleyGroup K)}
    (hu : u ∈ U0 K) (x : Ix3 → K) : g2Act u x ∈ S ↔ x ∈ S := by
  refine ⟨fun h => ?_, fun h => hS u hu x h⟩
  have := hS u⁻¹ ((U0 K).inv_mem hu) _ h
  rwa [g2Act_inv_apply] at this

theorem conj_g2Act (g u : ↥(cayleyGroup K)) (x : Ix3 → K) :
    g2Act g⁻¹ (g2Act (g * u * g⁻¹) x) = g2Act u (g2Act g⁻¹ x) := by
  rw [← g2Act_mul_apply, ← g2Act_mul_apply, show g⁻¹ * (g * u * g⁻¹) = u * g⁻¹ by group]

section Flag

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem IsCoord.rhoG_mem_stabW_iff (hf : IsCoord (lmG K) H Z π f) {c : K} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) {U : Subgroup W} (hZU : Z ≤ U) (g : ↥(cayleyGroup K)) :
    ((rhoG hc0 hc1 π g : ↥H) : MulAut W) ∈ Ch11.SecA.stabW U ↔
      ∀ y, y ∈ hf.img U ↔ g2Act g y ∈ hf.img U :=
  hf.mem_stabW_iff hZU _

theorem isFlagW_preG (hW : ∀ w : W, w ^ 2 = 1) (hf : IsCoord (lmG K) H Z π f) {c : K}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) {P : Subgroup (MulAut W)} {g : ↥(cayleyGroup K)}
    (hg : ∀ x : MulAut W,
      x ∈ P ↔ ∃ u ∈ U0 K, x = ((rhoG hc0 hc1 π (g * u * g⁻¹) : ↥H) : MulAut W))
    {S : Submodule K (Ix3 → K)} (hS : U0Stable S) {i : ℕ} (hcard : Nat.card S = Nat.card K ^ i) :
    Ch11.SecA.IsFlagW H P Z (Nat.card K) i (hf.pre (gmapG g S).toAddSubgroup) := by
  refine ⟨hf.le_pre _, ?_, ?_, fun x hx => ?_⟩
  · rw [hf.endStableW_iff hW (fun T hT => commutant_g2Derived hc0 hc1 _ T hT) (hf.le_pre _),
      hf.img_pre]
    exact fun c x hx => (gmapG g S).smul_mem c hx
  · rw [← hf.card_img, hf.img_pre, ← hcard, ← card_gmapG g S]
    rfl
  · obtain ⟨u, hu, rfl⟩ := (hg x).mp hx
    rw [IsCoord.rhoG_mem_stabW_iff hf hc0 hc1 (hf.le_pre _), hf.img_pre]
    intro y
    change y ∈ gmapG g S ↔ _ ∈ gmapG g S
    rw [mem_gmapG, mem_gmapG, conj_g2Act, hS.mem_iff hu]

theorem exists_eq_preG_of_isFlagW (hW : ∀ w : W, w ^ 2 = 1) (hf : IsCoord (lmG K) H Z π f)
    {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {P : Subgroup (MulAut W)} {g : ↥(cayleyGroup K)}
    (hg : ∀ x : MulAut W,
      x ∈ P ↔ ∃ u ∈ U0 K, x = ((rhoG hc0 hc1 π (g * u * g⁻¹) : ↥H) : MulAut W))
    {i : ℕ} {U : Subgroup W} (hU : Ch11.SecA.IsFlagW H P Z (Nat.card K) i U) :
    ∃ S : Submodule K (Ix3 → K), U0Stable S ∧ Nat.card S = Nat.card K ^ i ∧
      U = hf.pre (gmapG g S).toAddSubgroup := by
  obtain ⟨hZU, hst, hidx, hPU⟩ := hU
  have hsc := (hf.endStableW_iff hW (fun T hT => commutant_g2Derived hc0 hc1 _ T hT)
    hZU).mp hst
  let T : Submodule K (Ix3 → K) :=
    { carrier := hf.img U
      add_mem' := (hf.img U).add_mem
      zero_mem' := (hf.img U).zero_mem
      smul_mem' := fun c x hx => hsc c x hx }
  have hTcard : Nat.card T = Nat.card K ^ i := by
    rw [← hidx, ← hf.card_img]
    rfl
  refine ⟨gmapG g⁻¹ T, fun u hu x hx => ?_, by rw [card_gmapG, hTcard], ?_⟩
  · rw [mem_gmapG, inv_inv] at hx ⊢
    have hp : ((rhoG hc0 hc1 π (g * u * g⁻¹) : ↥H) : MulAut W) ∈ Ch11.SecA.stabW U :=
      hPU ((hg _).mpr ⟨u, hu, rfl⟩)
    have h1 := ((IsCoord.rhoG_mem_stabW_iff hf hc0 hc1 hZU _).mp hp _).mp hx
    change _ ∈ T at h1
    rw [← g2Act_mul_apply, show g * u * g⁻¹ * g = g * u by group, g2Act_mul_apply] at h1
    exact h1
  · rw [gmapG_gmapG_inv]
    exact (hf.pre_img hZU).symm

end Flag

omit [CharP K 2] in
theorem exists_ne_zero_ne_one_of_card [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 :=
  exists_ne_zero_ne_one (by
    rw [hK]
    calc 2 < 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)

theorem factFlagG2_holds : Ch11.SecA.FactFlagG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  rw [← hK]
  refine ⟨_, _, _, isFlagW_preG hW hf hc0 hc1 hg (stdF_stable 1) (card_stdF (by norm_num)),
    isFlagW_preG hW hf hc0 hc1 hg (stdF_stable 2) (card_stdF (by norm_num)),
    isFlagW_preG hW hf hc0 hc1 hg (stdF_stable 3) (card_stdF (by norm_num)),
    fun w hw => Submodule.map_mono (stdF_mono (by norm_num)) hw,
    fun w hw => Submodule.map_mono (stdF_mono (by norm_num)) hw,
    fun U hU => ?_, fun U hU => ?_, fun U hU => ?_⟩
  · obtain ⟨S, hS, hc, rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU
    rw [eq_stdF_of_card hS hc]
  · obtain ⟨S, hS, hc, rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU
    rw [eq_stdF_of_card hS hc]
  · obtain ⟨S, hS, hc, rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU
    rw [eq_stdF_of_card hS hc]

end CFSG.Quasithin.Vol2.Ch11.G2Q8
