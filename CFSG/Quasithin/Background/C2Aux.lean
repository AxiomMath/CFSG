
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Block
public import CFSG.Quasithin.Background.C2Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

omit [Finite G] in
private theorem c2aux_pCoreOf_eq_map (K : Subgroup G) :
    pCoreOf 2 K = (CFSG.pCore 2 ↥K).map K.subtype := by
  unfold pCoreOf
  try with_reducible rfl

omit [Finite G] in
private theorem c2aux_conj_mem_centralizer {S : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (hc : c ∈ Subgroup.centralizer (S : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
  have key := hc _ hs'
  calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * s := by group

omit [Finite G] in
private theorem c2aux_pPrimeCore_eq_bot (hO : oddCoreIn H = ⊥) : CFSG.pPrimeCore 2 ↥H = ⊥ := by
  have h1 : fusionOddCore ↥H = ⊥ := by
    unfold oddCoreIn at hO
    exact (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hO
  rw [← h1]
  unfold CFSG.pPrimeCore fusionOddCore
  congr 1
  ext K
  show (K.Normal ∧ Nat.Coprime 2 (Nat.card K)) ↔ (K.Normal ∧ Odd (Nat.card K))
  rw [Nat.coprime_two_left]

private theorem c2aux_charTwo_preimage (hO : oddCoreIn H = ⊥)
    (N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) [N.Normal] (hnil : Group.IsNilpotent N) :
    CharTwo (preimageModTwoCore H N) := by
  classical
  set Q₀ : Subgroup ↥H := CFSG.pCore 2 ↥H with hQ₀
  set π : ↥H →* (↥H ⧸ Q₀) := QuotientGroup.mk' Q₀ with hπ
  set Y' : Subgroup ↥H := N.comap π with hY'
  have hY'n : Y'.Normal := Subgroup.Normal.comap inferInstance π
  set Y : Subgroup G := preimageModTwoCore H N with hY
  have hYdef : Y = Y'.map H.subtype := rfl
  have hYH : Y ≤ H := by rw [hYdef]; exact Subgroup.map_subtype_le _
  have hQ : pCoreOf 2 H = Q₀.map H.subtype := c2aux_pCoreOf_eq_map H
  have hQ₀Y' : Q₀ ≤ Y' := by
    intro x hx
    rw [hY', Subgroup.mem_comap, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact N.one_mem
  have hQY : pCoreOf 2 H ≤ Y := by
    rw [hQ, hYdef]
    exact Subgroup.map_mono hQ₀Y'
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) := by
    have : (Y.subgroupOf H).Normal := by
      have h1 : Y.subgroupOf H = Y' := by
        rw [hYdef]
        exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y'
      rw [h1]
      exact hY'n
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mp this
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hOY : pCoreOf 2 Y = pCoreOf 2 H := by
    refine le_antisymm ?_ ?_
    · refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYH) ?_ (pCoreOf_isPGroup 2 Y)
      exact hHY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
    · exact le_pCoreOf_of_le_normalizer 2 hQY (hYH.trans hHQ) (pCoreOf_isPGroup 2 H)
  unfold CharTwo
  rw [hOY]
  set Z : Subgroup G := Y ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) with hZ
  have hZH : Z ≤ H := inf_le_left.trans hYH
  have hZnorm : H ≤ Subgroup.normalizer (Z : Set G) := by
    intro h hh
    have hhY := hHY hh
    have hhQ := hHQ hh
    have hhC : h ∈ Subgroup.normalizer (Subgroup.centralizer (pCoreOf 2 H : Set G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact c2aux_conj_mem_centralizer hhQ hx
      · intro hx
        have := c2aux_conj_mem_centralizer (Subgroup.inv_mem _ hhQ) hx
        simpa [mul_assoc] using this
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hhY, hhC⟩
  have hZ'n : (Z.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZH).mpr hZnorm
  have hZY : Z ≤ Y := inf_le_left
  have hrange : ∀ z : ↥Z, π (Subgroup.inclusion hZH z) ∈ N := by
    intro z
    have hz : (z : G) ∈ Y'.map H.subtype := by rw [← hYdef]; exact hZY z.2
    obtain ⟨y, hy, hyz⟩ := hz
    have : Subgroup.inclusion hZH z = y := Subtype.ext hyz.symm
    rw [this]
    exact hy
  let φ : ↥Z →* ↥N := (π.comp (Subgroup.inclusion hZH)).codRestrict N hrange
  have hker : φ.ker ≤ Subgroup.center ↥Z := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hz1 : π (Subgroup.inclusion hZH z) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
      simpa [φ] using this
    have hzQ : (z : G) ∈ pCoreOf 2 H := by
      rw [hQ]
      exact ⟨Subgroup.inclusion hZH z, (QuotientGroup.eq_one_iff _).mp hz1, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp w.2.2 (z : G) hzQ
    exact Subtype.ext this.symm
  have hZnil : Group.IsNilpotent ↥Z := Subgroup.isNilpotent_of_ker_le_center φ hker
  have hZ'nil : Group.IsNilpotent ↥(Z.subgroupOf H) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hZH).symm
  have hZ'le : Z.subgroupOf H ≤ CFSG.fittingSubgroup ↥H := le_sSup ⟨hZ'n, hZ'nil⟩
  rw [CFSG.Fitting_eq_pcore ↥H 2 (c2aux_pPrimeCore_eq_bot hO)] at hZ'le
  rw [hQ, ← Subgroup.map_subgroupOf_eq_of_le hZH]
  exact Subgroup.map_mono hZ'le

theorem charTwo_oTwoThreeIn_of_oddCore_eq_bot (hO : oddCoreIn H = ⊥) :
    CharTwo (oTwoThreeIn H) :=
  c2aux_charTwo_preimage hO (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))
    (CFSG.pCore_isPGroup (p := 3)).isNilpotent

theorem charTwo_oTwoFIn_of_oddCore_eq_bot (hO : oddCoreIn H = ⊥) : CharTwo (oTwoFIn H) :=
  c2aux_charTwo_preimage hO (CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)) inferInstance

omit [Finite G] in
private theorem c2aux_blockQ_map (e : G ≃* G) (K : Subgroup G) :
    blockQ (K.map e.toMonoidHom) = (blockQ K).map e.toMonoidHom :=
  pCoreOf_map_mulEquiv 2 e K

omit [Finite G] in
private theorem c2aux_blockU_map (e : G ≃* G) (K : Subgroup G) :
    blockU (K.map e.toMonoidHom) = (blockU K).map e.toMonoidHom := by
  unfold blockU
  rw [c2aux_blockQ_map, Subgroup.map_commutator]

omit [Finite G] in
private theorem c2aux_mem_map {e : G ≃* G} {K : Subgroup G} {x : G} :
    x ∈ K.map e.toMonoidHom ↔ e.symm x ∈ K := Subgroup.mem_map_equiv

omit [Finite G] in
private theorem c2aux_blockZ_map (e : G ≃* G) (K : Subgroup G) :
    blockZ (K.map e.toMonoidHom) = (blockZ K).map e.toMonoidHom := by
  ext x
  rw [c2aux_mem_map]
  unfold blockZ
  rw [c2aux_blockU_map]
  simp only [Subgroup.mem_inf, c2aux_mem_map]
  apply and_congr_right
  intro _
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have := h (e k) (c2aux_mem_map.mpr (by simpa using hk))
    simpa using congrArg e.symm this
  · intro h k hk
    have := h (e.symm k) (c2aux_mem_map.mp hk)
    simpa using congrArg e this

omit [Finite G] in
private theorem c2aux_isShort2_map (e : G ≃* G) {K : Subgroup G} (hK : IsShort2 K) :
    IsShort2 (K.map e.toMonoidHom) := by
  obtain ⟨h1, h2, ⟨h3a, h3b⟩, h4, h5a, h5b⟩ := hK
  unfold IsShort2
  set φ : ↥K ≃* ↥(K.map e.toMonoidHom) := e.subgroupMap K with hφ
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  ·
    intro N' hN' hp
    have hN'map : (N'.comap φ.toMonoidHom).map φ.toMonoidHom = N' :=
      Subgroup.map_comap_eq_self_of_surjective φ.surjective N'
    have hNn : (N'.comap φ.toMonoidHom).Normal := hN'.comap φ.toMonoidHom
    let ψ := QuotientGroup.congr (N'.comap φ.toMonoidHom) N' φ hN'map
    have hp' : IsPGroup 2 (↥K ⧸ N'.comap φ.toMonoidHom) := hp.of_equiv ψ.symm
    have htop := h1 _ hp'
    rw [← hN'map, htop, Subgroup.map_top_of_surjective _ φ.surjective]
  ·
    unfold CharTwo at h2 ⊢
    rw [pCoreOf_map_mulEquiv 2 e K]
    rintro x ⟨hxK, hxC⟩
    obtain ⟨y, hy, rfl⟩ := hxK
    refine ⟨y, h2 ⟨hy, Subgroup.mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro q hq
    have := Subgroup.mem_centralizer_iff.mp hxC (e q) ⟨q, hq, rfl⟩
    exact e.injective (by simpa using this)
  ·
    rw [c2aux_blockU_map, c2aux_blockQ_map]
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨huQ, huC⟩ := Subgroup.mem_inf.mp (h3a hu)
    refine ⟨⟨u, huQ, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp huC q hq
    simpa using congrArg e this
  ·
    rw [c2aux_blockU_map]
    rintro _ ⟨u, hu, rfl⟩
    change e u ^ 2 = 1
    rw [← map_pow, h3b u hu, map_one]
  ·
    have hmap : (CFSG.pCore 2 ↥K).map φ.toMonoidHom = CFSG.pCore 2 ↥(K.map e.toMonoidHom) :=
      CFSG.pCore_map_iso 2 φ
    let ψ : ↥K ⧸ CFSG.pCore 2 ↥K ≃*
        ↥(K.map e.toMonoidHom) ⧸ CFSG.pCore 2 ↥(K.map e.toMonoidHom) :=
      QuotientGroup.congr _ _ φ hmap
    rcases h4 with hq | hc
    · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv ψ hq)
    · exact Or.inr (by rw [← Nat.card_congr ψ.toEquiv]; exact hc)
  ·
    rw [c2aux_blockZ_map, c2aux_blockU_map]
    exact (Subgroup.map_lt_map_iff_of_injective e.injective).mpr h5a
  ·
    intro W hZW hWU hKW
    rw [c2aux_blockZ_map] at hZW ⊢
    rw [c2aux_blockU_map] at hWU ⊢
    set W₀ : Subgroup G := W.comap e.toMonoidHom with hW₀
    have hWeq : W₀.map e.toMonoidHom = W :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective W
    have h1' : blockZ K ≤ W₀ := fun z hz => hZW ⟨z, hz, rfl⟩
    have h2' : W₀ ≤ blockU K := by
      intro w hw
      obtain ⟨u, hu, hue⟩ := hWU hw
      have : u = w := e.injective hue
      rwa [← this]
    have h3' : K ≤ Subgroup.normalizer (W₀ : Set G) :=
      (Subgroup.map_le_iff_le_comap.mp hKW).trans (Subgroup.le_normalizer_comap e.toMonoidHom)
    rcases h5b W₀ h1' h2' h3' with h | h
    · left; rw [← hWeq, h]
    · right; rw [← hWeq, h]

omit [Finite G] in
theorem IsBlock2.conjByElt_of_mem {B : Subgroup G} (hB : IsBlock2 H B) {g : G} (hg : g ∈ H) :
    IsBlock2 H (conjByElt g B) := by
  obtain ⟨hshort, hBH, hsub⟩ := hB
  refine ⟨c2aux_isShort2_map (MulAut.conj g) hshort, ?_, ?_⟩
  · intro x hx
    have hx' : g⁻¹ * x * g ∈ B := mem_conjByElt.mp hx
    have := H.mul_mem (H.mul_mem hg (hBH hx')) (H.inv_mem hg)
    simpa [mul_assoc] using this
  · have hEq : (conjByElt g B).subgroupOf H =
        (B.subgroupOf H).map (MulAut.conj (⟨g, hg⟩ : H)).toMonoidHom := by
      ext x
      rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, mem_conjByElt, Subgroup.mem_subgroupOf]
      simp [MulAut.conj_symm_apply]
    rw [hEq]
    exact Subgroup.IsSubnormal.map (MulAut.conj _).surjective hsub

omit [Finite G] in
private theorem c2aux_exists_lift {B : Subgroup G} {S : Type*} [Group S]
    (α : ↥B →* S) (hα : Function.Surjective α) (hk : IsPGroup 2 α.ker) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {s : S} (hs : s ^ p = 1) (hs1 : s ≠ 1) (hsc : s ∉ Subgroup.center S) :
    ∃ x ∈ B, orderOf x = p ∧ x ∉ centerOf B := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, rfl⟩ := hα s
  have hyp : y ^ p ∈ α.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hs
  obtain ⟨k, hk'⟩ := hk ⟨y ^ p, hyp⟩
  have hk2 : (y ^ p) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk'
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  set e := 2 ^ k * m with he
  have heq : e = p * (e / p) + 1 := by
    have := Nat.div_add_mod e p
    omega
  have hαe : α (y ^ e) = α y := by
    rw [map_pow, heq, pow_succ, pow_mul, hs, one_pow, one_mul]
  have hye : (y ^ e) ^ p = 1 := by
    have : (y ^ e) ^ p = ((y ^ p) ^ 2 ^ k) ^ m := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, he]
      congr 1
      ring
    rw [this, hk2, one_pow]
  have hy1 : y ^ e ≠ 1 := by
    intro h
    rw [h, map_one] at hαe
    exact hs1 hαe.symm
  refine ⟨((y ^ e : ↥B) : G), (y ^ e).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hye hy1
  · intro hx
    apply hsc
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨b, rfl⟩ := hα g
    have hb := Subgroup.mem_centralizer_iff.mp hx.2 (b : G) b.2
    have hb' : b * y ^ e = y ^ e * b := Subtype.ext hb
    have := congrArg α hb'
    rw [map_mul, map_mul, hαe] at this
    exact this

private noncomputable def c2auxDiagFun (F : Type) [Field F] (a : Fˣ) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩

private theorem c2auxDiagFun_mul (F : Type) [Field F] (a b : Fˣ) :
    c2auxDiagFun F (a * b) = c2auxDiagFun F a * c2auxDiagFun F b := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [c2auxDiagFun, mul_comm]

private noncomputable def c2auxDiag (F : Type) [Field F] :
    Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F :=
  MonoidHom.mk' (c2auxDiagFun F) (c2auxDiagFun_mul F)

private def c2auxTransv (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem c2auxDiag_ne_one (F : Type) [Field F] {a : Fˣ} (ha : a ≠ 1) :
    c2auxDiag F a ≠ 1 := by
  intro h
  have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  apply ha
  apply Units.ext
  simpa [c2auxDiag, c2auxDiagFun] using h00

private theorem c2auxDiag_not_comm (F : Type) [Field F] {a : Fˣ} (ha : a ≠ a⁻¹) :
    c2auxDiag F a * c2auxTransv F ≠ c2auxTransv F * c2auxDiag F a := by
  intro h
  have h01 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h01
  simp [c2auxDiag, c2auxDiagFun, c2auxTransv, Matrix.mul_apply, Fin.sum_univ_two] at h01
  exact ha (Units.ext (by rw [Units.val_inv_eq_inv_val]; exact h01))

private theorem c2aux_exists_alt5_threeCycle :
    ∃ s : alternatingGroup (Fin 5), s ^ 3 = 1 ∧ s ≠ 1 ∧
      s ∉ Subgroup.center (alternatingGroup (Fin 5)) := by
  let f : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2
  let g : Equiv.Perm (Fin 5) := Equiv.swap 0 3 * Equiv.swap 3 4
  have hf : f ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have hg : g ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 (by decide)
  refine ⟨⟨f, hf⟩, ?_, ?_, ?_⟩
  · refine Subtype.ext ?_
    change f ^ 3 = 1
    decide
  · intro h
    have := congrArg Subtype.val h
    change f = 1 at this
    revert this
    decide
  · intro h
    have := Subgroup.mem_center_iff.mp h ⟨g, hg⟩
    have h2 := congrArg Subtype.val this
    change g * f = f * g at h2
    revert h2
    decide

theorem exists_noncentral_odd_prime_of_isChi0Block {X B : Subgroup G} (hB : IsChi0Block X B) :
    ∃ x ∈ B, (orderOf x).Prime ∧ orderOf x ≠ 2 ∧ x ∉ centerOf B := by
  obtain ⟨⟨hshort, -, -⟩, hty⟩ := hB
  rcases hty with ⟨n, hn, hlin⟩ | h3 | h5
  ·
    obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, -⟩ := hlin
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hcardU : Nat.card Fˣ = 2 ^ n - 1 := by
      rw [Nat.card_units, Nat.card_eq_fintype_card, hcard]
    have hne1 : 2 ^ n - 1 ≠ 1 := by omega
    have hpp : (2 ^ n - 1).minFac.Prime := Nat.minFac_prime hne1
    have hpd : (2 ^ n - 1).minFac ∣ 2 ^ n - 1 := Nat.minFac_dvd _
    set p := (2 ^ n - 1).minFac with hp
    have hp2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpd
      have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rw [hcardU]; exact hpd)
    have hap : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
    have ha1 : a ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ha
      exact hpp.one_lt.ne ha
    have hainv : a ≠ a⁻¹ := by
      intro h
      have h2 : a ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr h
      have : p ∣ 2 := ha ▸ orderOf_dvd_of_pow_eq_one h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
    have hs : c2auxDiag F a ^ p = 1 := by rw [← map_pow, hap, map_one]
    have hsc : c2auxDiag F a ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      intro h
      exact c2auxDiag_not_comm F hainv (Subgroup.mem_center_iff.mp h (c2auxTransv F)).symm
    obtain ⟨x, hxB, hxo, hxc⟩ := c2aux_exists_lift α hαs
      (by rw [hαk]; exact CFSG.pCore_isPGroup) hpp hp2 hs (c2auxDiag_ne_one F ha1) hsc
    exact ⟨x, hxB, hxo ▸ hpp, by rw [hxo]; exact hp2, hxc⟩
  ·
    obtain ⟨-, hcardU, -, -, -, -, c, hcB, hc3, -, hcfix, hBeq⟩ := hshort.alt3_structure h3
    refine ⟨c, hcB, by rw [hc3]; exact Nat.prime_three, by rw [hc3]; norm_num, ?_⟩
    intro hc
    have hUB : blockU B ≤ B := le_sup_left.trans hBeq.ge
    have hne : blockU B ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hcardU
      omega
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    have := Subgroup.mem_centralizer_iff.mp hc.2 u (hUB hu)
    apply hcfix u hu hu1'
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  ·
    obtain ⟨α, hαs, hαk, -⟩ := h5
    obtain ⟨s, hs3, hs1, hsc⟩ := c2aux_exists_alt5_threeCycle
    obtain ⟨x, hxB, hxo, hxc⟩ := c2aux_exists_lift α hαs
      (by rw [hαk]; exact CFSG.pCore_isPGroup) Nat.prime_three (by norm_num) hs3 hs1 hsc
    exact ⟨x, hxB, hxo ▸ Nat.prime_three, by rw [hxo]; norm_num, hxc⟩

theorem perfect_le_centralizer_of_isAltType_three {X P : Subgroup G} (hX : IsShort2 X)
    (h3 : IsAltType X 3) (hPN : P ≤ Subgroup.normalizer (X : Set G)) (hP : ⁅P, P⁆ = P) :
    P ≤ Subgroup.centralizer (X : Set G) := by
  obtain ⟨hQU, hcardU, -, hcomm, hcardX, -, c, hcX, -, -, hcfix, hXeq⟩ := hX.alt3_structure h3
  have hUQ : pCoreOf 2 X = blockU X := hQU
  have hPU : P ≤ Subgroup.normalizer (blockU X : Set G) := by
    rw [← hUQ]; exact hPN.trans (normalizer_le_normalizer_pCoreOf 2 X)
  have hXU : X ≤ Subgroup.normalizer (blockU X : Set G) := by
    rw [← hUQ]; exact le_normalizer_pCoreOf 2 X
  have hUX : blockU X ≤ X := le_sup_left.trans hXeq.ge
  have hPperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have hPcU : P ≤ Subgroup.centralizer (blockU X : Set G) := by
    have : Group.IsSolvable (Equiv.Perm ↥(blockU X)) := Equiv.Perm.isSolvable (by rw [hcardU])
    let φ : ↥P →* Equiv.Perm ↥(blockU X) := (MulAut.toPerm ↥(blockU X)).comp
      ((blockU X).normalizerMonoidHom.comp (Subgroup.inclusion hPU))
    have hr : φ.range = ⊥ := by
      by_contra hne
      have : Nontrivial φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
      exact Group.IsPerfect.not_isSolvable (G := φ.range) inferInstance
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : φ ⟨p, hp⟩ = 1 := by
      have : φ ⟨p, hp⟩ ∈ φ.range := ⟨_, rfl⟩
      rw [hr] at this
      exact this
    have h2 : p * u * p⁻¹ = u := congrArg (fun f => ((f ⟨u, hu⟩ : ↥(blockU X)) : G)) h1
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hCX : X ⊓ Subgroup.centralizer (blockU X : Set G) = blockU X := by
    have hUC : blockU X ≤ X ⊓ Subgroup.centralizer (blockU X : Set G) := by
      refine le_inf hUX fun u hu => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact hcomm v hv u hu
    have hd1 : Nat.card ↥(blockU X) ∣ Nat.card ↥(X ⊓ Subgroup.centralizer (blockU X : Set G)) :=
      Subgroup.card_dvd_of_le hUC
    have hd2 : Nat.card ↥(X ⊓ Subgroup.centralizer (blockU X : Set G)) ∣ Nat.card ↥X :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [hcardU] at hd1
    rw [hcardX] at hd2
    have hle12 : Nat.card ↥(X ⊓ Subgroup.centralizer (blockU X : Set G)) ≤ 12 :=
      Nat.le_of_dvd (by norm_num) hd2
    have hcases : Nat.card ↥(X ⊓ Subgroup.centralizer (blockU X : Set G)) = 4 ∨
        Nat.card ↥(X ⊓ Subgroup.centralizer (blockU X : Set G)) = 12 := by
      generalize Nat.card ↥(X ⊓ Subgroup.centralizer (blockU X : Set G)) = n at hd1 hd2 hle12
      interval_cases n <;> omega
    rcases hcases with h4 | h12
    · exact (Subgroup.eq_of_le_of_card_ge hUC (by rw [h4, hcardU])).symm
    · exfalso
      have hCeq : X ⊓ Subgroup.centralizer (blockU X : Set G) = X :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h12, hcardX])
      have hcC : c ∈ Subgroup.centralizer (blockU X : Set G) := by
        have : c ∈ X ⊓ Subgroup.centralizer (blockU X : Set G) := hCeq.ge hcX
        exact this.2
      have hne : (blockU X) ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcardU
        omega
      obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
      have := Subgroup.mem_centralizer_iff.mp hcC u hu
      apply hcfix u hu hu1'
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
  have hPX : ⁅P, X⁆ ≤ blockU X := by
    rw [Subgroup.commutator_le]
    intro p hp x hx
    have hpX : p * x * p⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hPN hp) x).mp hx
    have hmem : ⁅p, x⁆ ∈ X ⊓ Subgroup.centralizer (blockU X : Set G) := by
      refine ⟨X.mul_mem hpX (X.inv_mem hx), Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro u hu
      have hw : x⁻¹ * u * x ∈ blockU X := by
        have := (Subgroup.mem_normalizer_iff.mp (hXU (X.inv_mem hx)) u).mp hu
        simpa using this
      have hpu : p * u = u * p := (Subgroup.mem_centralizer_iff.mp (hPcU hp) u hu).symm
      have hpw : p * (x⁻¹ * u * x) = (x⁻¹ * u * x) * p :=
        (Subgroup.mem_centralizer_iff.mp (hPcU hp) _ hw).symm
      have hxw : x * (x⁻¹ * u * x) = u * x := by group
      have hxu : x⁻¹ * u = (x⁻¹ * u * x) * x⁻¹ := by group
      have hpiw : p⁻¹ * (x⁻¹ * u * x) = (x⁻¹ * u * x) * p⁻¹ := by
        calc p⁻¹ * (x⁻¹ * u * x) = p⁻¹ * ((x⁻¹ * u * x) * p) * p⁻¹ := by group
          _ = p⁻¹ * (p * (x⁻¹ * u * x)) * p⁻¹ := by rw [hpw]
          _ = (x⁻¹ * u * x) * p⁻¹ := by group
      rw [commutatorElement_def]
      calc u * (p * x * p⁻¹ * x⁻¹) = (u * p) * x * p⁻¹ * x⁻¹ := by group
        _ = (p * u) * x * p⁻¹ * x⁻¹ := by rw [hpu]
        _ = p * (u * x) * p⁻¹ * x⁻¹ := by group
        _ = p * (x * (x⁻¹ * u * x)) * p⁻¹ * x⁻¹ := by rw [hxw]
        _ = p * x * ((x⁻¹ * u * x) * p⁻¹) * x⁻¹ := by group
        _ = p * x * (p⁻¹ * (x⁻¹ * u * x)) * x⁻¹ := by rw [hpiw]
        _ = p * x * p⁻¹ * ((x⁻¹ * u * x) * x⁻¹) := by group
        _ = p * x * p⁻¹ * (x⁻¹ * u) := by rw [← hxu]
        _ = p * x * p⁻¹ * x⁻¹ * u := by group
    rw [← hCX]
    exact hmem
  have h1 : ⁅⁅P, X⁆, P⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅P, X⁆, P⁆ ≤ ⁅blockU X, P⁆ := Subgroup.commutator_mono hPX le_rfl
      _ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hPcU
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.LocalCores.perfect_double_commutator hPperf h1)

end CFSG.Quasithin
