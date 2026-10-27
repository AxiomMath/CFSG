module

public import CFSG.Quasithin.EmptyFaithful.S14612EB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.QuasithinUnique (IsSylowTwoOf)

section Split

variable {W : Type} [CommGroup W] [Finite W] {X P Tb : Subgroup (MulAut W)}

omit [Finite W] in
theorem exists_mul_of_normalizes {P Tb : Subgroup (MulAut W)}
    (hT : Tb ≤ Subgroup.normalizer (P : Set (MulAut W))) {g : MulAut W} (hg : g ∈ P ⊔ Tb) :
    ∃ a ∈ P, ∃ t ∈ Tb, g = a * t := by
  let S : Subgroup (MulAut W) :=
    { carrier := {g | ∃ a ∈ P, ∃ t ∈ Tb, g = a * t}
      one_mem' := ⟨1, P.one_mem, 1, Tb.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, t, ht, rfl⟩ ⟨a', ha', t', ht', rfl⟩
        have h1 : t * a' * t⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hT ht) a').mp ha'
        refine ⟨a * (t * a' * t⁻¹), P.mul_mem ha h1, t * t', Tb.mul_mem ht ht', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨a, ha, t, ht, rfl⟩
        have h1 : t⁻¹ * a⁻¹ * t ∈ P := by
          have := (Subgroup.mem_normalizer_iff.mp (hT (Tb.inv_mem ht)) a⁻¹).mp (P.inv_mem ha)
          simpa using this
        refine ⟨t⁻¹ * a⁻¹ * t, h1, t⁻¹, Tb.inv_mem ht, ?_⟩
        group }
  exact (sup_le (fun a ha => ⟨a, ha, 1, Tb.one_mem, by simp⟩)
    (fun t ht => ⟨1, P.one_mem, t, ht, by simp⟩) : P ⊔ Tb ≤ S) hg

theorem commV_inf_fixV_eq_bot (hW : ∀ w : W, w ^ 2 = 1) (hP : Odd (Nat.card P)) :
    commV P ⊓ fixV P = ⊥ := by
  have := (coprime_decomp hP hW (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)).2
  simpa [commV_eq_commSub] using this

theorem exists_split14612 (hW : ∀ w : W, w ^ 2 = 1) (hP : Odd (Nat.card P)) (hPn : NormalIn X P)
    (hPX : P ≤ X) (hXeq : X = P ⊔ Tb) {v : W} (hv : v ∈ fixV Tb)
    (hgen : Subgroup.closure {w | ∃ x ∈ X, w = x v} = ⊤) :
    ∃ v' ∈ commV P, ∃ c ∈ fixV X, v = v' * c ∧ v' ∈ fixV Tb ∧ commV X = commV P ∧
      commV P ⊔ fixV X = ⊤ ∧ commV P ⊓ fixV X = ⊥ ∧
      Subgroup.closure {w | ∃ x ∈ X, w = x v'} = commV P := by
  have hTbN : Tb ≤ Subgroup.normalizer (P : Set (MulAut W)) :=
    fun t ht => hPn.le_normalizer (hXeq ▸ (le_sup_right : Tb ≤ P ⊔ Tb) ht)
  have hinf := commV_inf_fixV_eq_bot hW hP
  set c : W := avgMap P v with hcdef
  have hcP : c ∈ fixV P := avgMap_mem_fixV P v
  have hvc : v * c ∈ commV P := by
    have := mul_avgMap_mem_commV hP hW v
    exact this
  have hsqc : c * c = 1 := by rw [← pow_two]; exact hW c
  have hcT : ∀ t ∈ Tb, t c = c := by
    intro t ht
    have htX : t ∈ X := hXeq ▸ (le_sup_right : Tb ≤ P ⊔ Tb) ht
    have h1 : t c ∈ fixV P := hPn.fixV_invariant htX hcP
    have h2 : v * t c ∈ commV P := by
      have h3 : t (v * c) ∈ commV P := hPn.commV_invariant htX hvc
      rwa [map_mul, hv t ht] at h3
    have h4 : (t c) * c⁻¹ ∈ commV P ⊓ fixV P := by
      refine ⟨?_, (fixV P).mul_mem h1 ((fixV P).inv_mem hcP)⟩
      have := (commV P).mul_mem h2 ((commV P).inv_mem hvc)
      have e : v * t c * (v * c)⁻¹ = t c * c⁻¹ := by
        rw [mul_inv_rev, mul_comm v (t c)]
        calc t c * v * (c⁻¹ * v⁻¹) = t c * c⁻¹ * (v * v⁻¹) := by
              simp only [mul_assoc, mul_comm, mul_left_comm]
          _ = t c * c⁻¹ := by simp
      rwa [e] at this
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h4
    exact h4
  have hcX : c ∈ fixV X := by
    intro x hx
    obtain ⟨a, ha, t, ht, rfl⟩ := exists_mul_of_normalizes hTbN (hXeq ▸ hx)
    have : (a * t) c = a (t c) := rfl
    rw [this, hcT t ht]
    exact hcP a ha
  set v' : W := v * c with hv'def
  have hv'v : v = v' * c := by rw [hv'def, mul_assoc, hsqc, mul_one]
  have hv'T : v' ∈ fixV Tb := fun t ht => by
    have : t (v * c) = t v * t c := map_mul t v c
    rw [hv'def, this, hv t ht, hcT t ht]
  have hKinv : ∀ x ∈ X, ∀ u ∈ commV P, x u ∈ commV P := fun x hx u hu =>
    hPn.commV_invariant hx hu
  have hmem : ∀ x ∈ X, x v ∈ commV P ⊔ Subgroup.zpowers c := by
    intro x hx
    rw [hv'v, map_mul, hcX x hx]
    exact (commV P ⊔ Subgroup.zpowers c).mul_mem
      (Subgroup.mem_sup_left (hKinv x hx _ hvc)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hW1 : commV P ⊔ Subgroup.zpowers c = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hmem x hx
  have hzf : ∀ z ∈ Subgroup.zpowers c, ∀ x ∈ X, x z = z := by
    intro z hz x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [map_zpow, hcX x hx]
  have hcommX : commV X = commV P := by
    apply le_antisymm
    · refine Subgroup.closure_le _ |>.mpr ?_
      rintro _ ⟨x, hx, w, rfl⟩
      have hw : w ∈ commV P ⊔ Subgroup.zpowers c := by rw [hW1]; exact Subgroup.mem_top w
      obtain ⟨k, hk, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
      have e : x (k * z) * (k * z)⁻¹ = x k * k⁻¹ := by
        rw [map_mul, hzf z hz x hx, mul_inv_rev]
        calc x k * z * (z⁻¹ * k⁻¹) = x k * (z * z⁻¹) * k⁻¹ := by simp only [mul_assoc]
          _ = x k * k⁻¹ := by simp
      show x (k * z) * (k * z)⁻¹ ∈ commV P
      rw [e]
      exact (commV P).mul_mem (hKinv x hx k hk) ((commV P).inv_mem hk)
    · exact commV_mono216 hPX
  have hsupfix : commV P ⊔ fixV X = ⊤ := by
    rw [eq_top_iff, ← hW1]
    exact sup_le_sup_left (Subgroup.zpowers_le.mpr hcX) _
  have hinfX : commV P ⊓ fixV X = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun w hw => ?_
    have : w ∈ commV P ⊓ fixV P := ⟨hw.1, fun a ha => hw.2 a (hPX ha)⟩
    rw [hinf] at this
    exact this
  refine ⟨v', hvc, c, hcX, hv'v, hv'T, hcommX, hsupfix, hinfX, ?_⟩
  set K' : Subgroup W := Subgroup.closure {w | ∃ x ∈ X, w = x v'} with hK'
  have hK'K : K' ≤ commV P := by
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hKinv x hx _ hvc
  have hK'inv : ∀ x ∈ X, ∀ u ∈ K', x u ∈ K' := by
    intro x hx u hu
    refine Subgroup.closure_induction (p := fun u _ => x u ∈ K') ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.subset_closure ⟨x * y, X.mul_mem hx hy, rfl⟩
    · simp
    · intro a b _ _ ha hb
      rw [map_mul]
      exact K'.mul_mem ha hb
    · intro a _ ha
      rw [map_inv]
      exact K'.inv_mem ha
  have hW2 : K' ⊔ Subgroup.zpowers c = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [hv'v, map_mul, hcX x hx]
    exact (K' ⊔ Subgroup.zpowers c).mul_mem
      (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨x, hx, rfl⟩))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  refine le_antisymm hK'K ?_
  intro k hk
  have hkW : k ∈ K' ⊔ Subgroup.zpowers c := by rw [hW2]; exact Subgroup.mem_top k
  obtain ⟨k', hk', z, hz, hkz⟩ := Subgroup.mem_sup.mp hkW
  have hzK : z ∈ commV P := by
    have : z = k'⁻¹ * k := by rw [← hkz]; group
    rw [this]
    exact (commV P).mul_mem ((commV P).inv_mem (hK'K hk')) hk
  have hzfix : z ∈ fixV X := fun x hx => hzf z hz x hx
  have hz1 : z = 1 := by
    have : z ∈ commV P ⊓ fixV X := ⟨hzK, hzfix⟩
    rw [hinfX] at this
    exact this
  rw [← hkz, hz1, mul_one]
  exact hk'

end Split

section Beta

open CFSG.Quasithin.S1417

variable {Hh : Type} [Group Hh] {W : Type} [CommGroup W] [Finite W]

@[expose] def kOf (ρ : Hh →* MulAut W) : Subgroup W := commV ρ.range

omit [Finite W] in
theorem rho_mem_stabSub (ρ : Hh →* MulAut W) (h : Hh) : ρ h ∈ stabSub (kOf ρ) :=
  mem_stabSub_of_forall (fun _ hu => commV_stable ρ.range ⟨h, rfl⟩ hu)
    (fun _ hu => commV_stable ρ.range (ρ.range.inv_mem ⟨h, rfl⟩) hu)

@[expose] noncomputable def resBeta (ρ : Hh →* MulAut W) : Hh →* MulAut ↥(kOf ρ) :=
  (resHom (kOf ρ)).comp (ρ.codRestrict (stabSub (kOf ρ)) (rho_mem_stabSub ρ))

omit [Finite W] in
theorem resBeta_apply (ρ : Hh →* MulAut W) (h : Hh) (k : ↥(kOf ρ)) :
    ((resBeta ρ h k : ↥(kOf ρ)) : W) = ρ h (k : W) := rfl

omit [Finite W] in
theorem ker_resBeta (ρ : Hh →* MulAut W)
    (hsplit : ∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c) :
    (resBeta ρ).ker = ρ.ker := by
  ext h
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hh
    refine MulEquiv.ext fun w => ?_
    obtain ⟨a, ha, c, hc, rfl⟩ := hsplit w
    have h1 : ρ h a = a := by
      have := congrArg (fun φ : MulAut ↥(kOf ρ) => ((φ ⟨a, ha⟩ : ↥(kOf ρ)) : W)) hh
      simpa [resBeta_apply] using this
    have h2 : ρ h c = c := hc (ρ h) ⟨h, rfl⟩
    show ρ h (a * c) = a * c
    rw [map_mul, h1, h2]
  · intro hh
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [resBeta_apply, hh]
    rfl

omit [Finite W] in
theorem range_resBeta (ρ : Hh →* MulAut W) :
    (resBeta ρ).range = autSub ρ.range (kOf ρ) := by
  ext φ
  rw [mem_autSub, MonoidHom.mem_range]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨⟨ρ h, rho_mem_stabSub ρ h⟩, ⟨h, rfl⟩, rfl⟩
  · rintro ⟨g, ⟨h, hh⟩, rfl⟩
    refine ⟨h, ?_⟩
    have : (⟨ρ h, rho_mem_stabSub ρ h⟩ : stabSub (kOf ρ)) = g := Subtype.ext hh
    rw [← this]
    rfl

omit [Finite W] in
theorem suppData_split (ρ : Hh →* MulAut W)
    (hsplit : ∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c)
    (hinf : kOf ρ ⊓ fixV ρ.range = ⊥) : SuppData ρ.range (kOf ρ) (fixV ρ.range) where
  sup := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨a, ha, c, hc, rfl⟩ := hsplit w
    exact Subgroup.mul_mem_sup ha hc
  inf := hinf
  stab := by
    rintro _ ⟨h, rfl⟩
    exact rho_mem_stabSub ρ h
  triv := fun g hg u hu => hu g hg

theorem qhat_resBeta_le (ρ : Hh →* MulAut W)
    (hsplit : ∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c)
    (hinf : kOf ρ ⊓ fixV ρ.range = ⊥) : qhatOf (resBeta ρ).range ≤ qOf ρ.range := by
  rw [range_resBeta, (suppData_split ρ hsplit hinf).qhatOf_eq]
  exact qhatOf_le_qOf _

theorem card_map_eq_of_ker_eq {G G' G'' : Type*} [Group G] [Group G'] [Group G'']
    {f : G →* G'} {g : G →* G''} (h : f.ker = g.ker) (A : Subgroup G) :
    Nat.card ↥(A.map f) = Nat.card ↥(A.map g) := by
  have h1 : Nat.card ↥(A.map f) = f.ker.relIndex A := (Subgroup.relIndex_ker A f).symm
  have h2 : Nat.card ↥(A.map g) = g.ker.relIndex A := (Subgroup.relIndex_ker A g).symm
  rw [h1, h2, h]

theorem pstr_of_hom {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (β : Hh →* MulAut V) (P0 T0 : Subgroup Hh) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk1 : ∀ x : Hh, β x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hk2 : ∀ S : Subgroup Hh, S.Normal → IsPGroup 2 S → ∀ x ∈ S, β x = 1)
    (hPn : P0.Normal) (hkerP : β.ker ≤ P0)
    (hpp : ∀ x ∈ P0, ∃ k : ℕ, β (x ^ p ^ k) = 1)
    (hHeq : P0 ⊔ T0 = ⊤) (hT2 : IsPGroup 2 T0) (hTi : ¬ 2 ∣ T0.index)
    (hmin : ∀ N : Subgroup Hh, N.Normal → β.ker ≤ N → N ≤ P0 → N = β.ker ∨ N = P0)
    (hlt : ¬ P0 ≤ β.ker) (hcard : Nat.card ↥(P0.map β) ≠ p)
    (hq : qhatOf β.range ≤ 2) (hsq : IsQuotientOfSQTKTC ↥β.range) :
    PStr14612 β.range (T0.map β) (P0.map β) p := by
  classical
  have hrange : β.range = P0.map β ⊔ T0.map β := by
    rw [MonoidHom.range_eq_map, ← hHeq, Subgroup.map_sup]
  refine ⟨hV, hp, hp2, ?_, Subgroup.map_le_range β P0, ?_, ?_, ?_, hrange, ?_, hcard, ?_, hsq, hq⟩
  ·
    refine ⟨Subgroup.map_le_range β T0, ?_, ?_⟩
    · rintro ⟨x, t, ht, rfl⟩
      obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
      refine ⟨k, Subtype.ext ?_⟩
      have : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
      simp [← map_pow, this]
    · intro hd
      have h1 : (T0.map β).subgroupOf β.range = T0.map β.rangeRestrict := by
        ext x
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        constructor
        · rintro ⟨t, ht, hx⟩
          exact ⟨t, ht, Subtype.ext hx⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨t, ht, rfl⟩
      rw [h1, Subgroup.index_map, MonoidHom.range_eq_top_of_surjective _ β.rangeRestrict_surjective,
        Subgroup.index_top, mul_one] at hd
      exact hTi (hd.trans (Subgroup.index_dvd_of_le le_sup_left))
  ·
    rintro _ ⟨h, rfl⟩ _ ⟨a, ha, rfl⟩
    exact ⟨h * a * h⁻¹, hPn.conj_mem a ha h, by simp⟩
  ·
    rintro ⟨x, a, ha, rfl⟩
    obtain ⟨k, hk⟩ := hpp a ha
    exact ⟨k, Subtype.ext (by simpa [map_pow] using hk)⟩
  · exact fun hb => hlt ((Subgroup.map_eq_bot_iff _).mp hb)
  ·
    intro N' hN'P hN'n
    have hNn : (N'.comap β).Normal :=
      ⟨fun n hn h => by
        show β (h * n * h⁻¹) ∈ N'
        rw [map_mul, map_mul, map_inv]
        exact hN'n _ ⟨h, rfl⟩ _ hn⟩
    have hkerN : β.ker ≤ N'.comap β := fun x hx => by
      show β x ∈ N'
      rw [MonoidHom.mem_ker.mp hx]
      exact N'.one_mem
    have hNP : N'.comap β ≤ P0 := by
      intro x hx
      obtain ⟨a, ha, hax⟩ := hN'P (show β x ∈ N' from hx)
      have hxa : x * a⁻¹ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hax, mul_inv_cancel]
      have : x = (x * a⁻¹) * a := by group
      rw [this]
      exact P0.mul_mem (hkerP hxa) ha
    have hmc : (N'.comap β).map β = N' := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr (hN'P.trans (Subgroup.map_le_range _ _))
    rcases hmin _ hNn hkerN hNP with h0 | h1
    · left
      rw [← hmc, h0]
      exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
    · right
      rw [← hmc, h1]
  ·
    have hSX : pCoreOf 2 β.range ≤ β.range := pCoreOf_le 2 _
    have hSn : (pCoreOf 2 β.range).subgroupOf β.range |>.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSX).mpr (le_normalizer_pCoreOf 2 _)
    have hS2 : IsPGroup 2 (pCoreOf 2 β.range) := pCoreOf_isPGroup 2 _
    have hS2' : IsPGroup 2 ((pCoreOf 2 β.range).subgroupOf β.range) :=
      hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
    let St : Subgroup Hh := ((pCoreOf 2 β.range).subgroupOf β.range).comap β.rangeRestrict
    have hStn : St.Normal := hSn.comap _
    have hSt2 : IsPGroup 2 St := by
      intro s
      have hs : β.rangeRestrict (s : Hh) ∈ (pCoreOf 2 β.range).subgroupOf β.range := s.2
      obtain ⟨k, hk⟩ := hS2' ⟨β.rangeRestrict (s : Hh), hs⟩
      have h1 : β ((s : Hh) ^ 2 ^ k) = 1 := by
        have h1' := congrArg (fun z : ↥((pCoreOf 2 β.range).subgroupOf β.range) =>
          ((z : ↥β.range) : MulAut V)) hk
        simpa [map_pow] using h1'
      obtain ⟨j, hj⟩ := hk1 _ h1
      refine ⟨k + j, Subtype.ext ?_⟩
      have h4 : (s : Hh) ^ 2 ^ (k + j) = 1 := by rw [pow_add, pow_mul]; exact hj
      simpa using h4
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨y, rfl⟩ := hSX hx
    have hy : y ∈ St := by
      show β.rangeRestrict y ∈ (pCoreOf 2 β.range).subgroupOf β.range
      exact hx
    rw [Subgroup.mem_bot]
    exact hk2 St hStn hSt2 y hy

theorem class_hom {Hh : Type} [Group Hh] [Finite Hh] (hW : ∀ w : W, w ^ 2 = 1)
    (ρ : Hh →* MulAut W) (P0 T0 : Subgroup Hh) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk1 : ∀ x : Hh, ρ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hk2 : ∀ S : Subgroup Hh, S.Normal → IsPGroup 2 S → ∀ x ∈ S, ρ x = 1)
    (hPn : P0.Normal) (hkerP : ρ.ker ≤ P0)
    (hpp : ∀ x ∈ P0, ∃ k : ℕ, ρ (x ^ p ^ k) = 1)
    (hHeq : P0 ⊔ T0 = ⊤) (hT2 : IsPGroup 2 T0) (hTi : ¬ 2 ∣ T0.index)
    (hmin : ∀ N : Subgroup Hh, N.Normal → ρ.ker ≤ N → N ≤ P0 → N = ρ.ker ∨ N = P0)
    (hlt : ¬ P0 ≤ ρ.ker) (hcard : Nat.card ↥(P0.map ρ) ≠ p)
    (hq : qOf ρ.range ≤ 2) (hsq : IsQuotientOfSQTKTC ↥ρ.range)
    {w₀ : W} (hw₀ : ∀ t ∈ T0, ρ t w₀ = w₀)
    (hgen : Subgroup.closure {w | ∃ h : Hh, w = ρ h w₀} = ⊤) :
    (p = 3 ∧ Nat.card ↥(T0.map ρ) = 4) ∨
      ∃ L₁ L₂ : Subgroup (MulAut ↥(kOf ρ)),
        Blocks14612 (resBeta ρ).range (T0.map (resBeta ρ)) (P0.map (resBeta ρ)) p L₁ L₂ := by
  classical
  set X : Subgroup (MulAut W) := ρ.range with hX
  set P : Subgroup (MulAut W) := P0.map ρ with hP
  set Tb : Subgroup (MulAut W) := T0.map ρ with hTb
  have hPX : P ≤ X := Subgroup.map_le_range ρ P0
  have hXeq : X = P ⊔ Tb := by
    rw [hX, hP, hTb, MonoidHom.range_eq_map, ← hHeq, Subgroup.map_sup]
  have hPn' : NormalIn X P := by
    rintro _ ⟨h, rfl⟩ _ ⟨a, ha, rfl⟩
    exact ⟨h * a * h⁻¹, hPn.conj_mem a ha h, by simp⟩
  have hPodd : Odd (Nat.card P) := by
    have : Fact p.Prime := ⟨hp⟩
    have hpg : IsPGroup p ↥P := by
      rintro ⟨x, a, ha, rfl⟩
      obtain ⟨k, hk⟩ := hpp a ha
      exact ⟨k, Subtype.ext (by simpa [map_pow] using hk)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hpg
    rw [hn]
    exact Odd.pow (hp.eq_two_or_odd'.resolve_left hp2)
  have hv : w₀ ∈ fixV Tb := by
    rintro _ ⟨t, ht, rfl⟩
    exact hw₀ t ht
  have hgen' : Subgroup.closure {w | ∃ x ∈ X, w = x w₀} = ⊤ := by
    rw [← hgen]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, hw⟩
      exact ⟨h, hw⟩
    · rintro ⟨h, hw⟩
      exact ⟨ρ h, ⟨h, rfl⟩, hw⟩
  obtain ⟨v', hv', c, hc, hvv, hv'T, hcommX, hsup, hinf, hK⟩ :=
    exists_split14612 hW hPodd hPn' hPX hXeq hv hgen'
  have hkOf : kOf ρ = commV P := hcommX
  have hsplit : ∀ w : W, ∃ a ∈ kOf ρ, ∃ c ∈ fixV ρ.range, w = a * c := by
    intro w
    have hw : w ∈ commV P ⊔ fixV X := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨a, ha, c, hc, hac⟩ := Subgroup.mem_sup.mp hw
    exact ⟨a, hkOf ▸ ha, c, hc, hac.symm⟩
  have hinfK : kOf ρ ⊓ fixV ρ.range = ⊥ := by rw [hkOf]; exact hinf
  have hkb : (resBeta ρ).ker = ρ.ker := ker_resBeta ρ hsplit
  have hV' : ∀ v : ↥(kOf ρ), v ^ 2 = 1 := fun v => Subtype.ext (hW v)
  have hstr : PStr14612 (resBeta ρ).range (T0.map (resBeta ρ)) (P0.map (resBeta ρ)) p := by
    refine pstr_of_hom hV' (resBeta ρ) P0 T0 hp hp2 ?_ ?_ hPn ?_ ?_ hHeq hT2 hTi ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have : x ∈ (resBeta ρ).ker := hx
      rw [hkb] at this
      exact hk1 x this
    · intro S hS hS2 x hx
      have h1 : x ∈ ρ.ker := hk2 S hS hS2 x hx
      rw [← hkb] at h1
      exact h1
    · rw [hkb]
      exact hkerP
    · intro x hx
      obtain ⟨k, hk⟩ := hpp x hx
      have h1 : x ^ p ^ k ∈ ρ.ker := hk
      rw [← hkb] at h1
      exact ⟨k, h1⟩
    · intro N hN hkN hNP
      rw [hkb] at hkN ⊢
      exact hmin N hN hkN hNP
    · rw [hkb]
      exact hlt
    · rw [card_map_eq_of_ker_eq hkb P0]
      exact hcard
    · exact (qhat_resBeta_le ρ hsplit hinfK).trans hq
    · exact isQuotientOfSQTK_of_mulEquiv
        ((suppData_split ρ hsplit hinfK).restrictEquiv.trans
          (MulEquiv.subgroupCongr (range_resBeta ρ).symm)) hsq
  have hfix : fixV (P0.map (resBeta ρ)) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun v hv => ?_
    have h1 : (v : W) ∈ fixV P := by
      rintro _ ⟨a, ha, rfl⟩
      have := congrArg (fun z : ↥(kOf ρ) => (z : W)) (hv (resBeta ρ a) ⟨a, ha, rfl⟩)
      simpa [resBeta_apply] using this
    have h2 : (v : W) ∈ commV P ⊓ fixV P := ⟨hkOf ▸ v.2, h1⟩
    rw [commV_inf_fixV_eq_bot hW hPodd, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hgenK : ∀ W' : Subgroup ↥(kOf ρ),
      (∀ g ∈ (resBeta ρ).range, ∀ z ∈ fixV (T0.map (resBeta ρ)), g z ∈ W') → W' = ⊤ := by
    intro W' hW'
    have hv'K : v' ∈ kOf ρ := hkOf ▸ hv'
    set z : ↥(kOf ρ) := ⟨v', hv'K⟩ with hz
    have hzfix : z ∈ fixV (T0.map (resBeta ρ)) := by
      rintro _ ⟨t, ht, rfl⟩
      refine Subtype.ext ?_
      rw [resBeta_apply]
      exact hv'T (ρ t) ⟨t, ht, rfl⟩
    have hmem : ∀ x ∈ X, x v' ∈ W'.map (kOf ρ).subtype := by
      rintro _ ⟨h, rfl⟩
      refine ⟨resBeta ρ h z, hW' _ ⟨h, rfl⟩ z hzfix, ?_⟩
      rfl
    have hKW : kOf ρ ≤ W'.map (kOf ρ).subtype := by
      have h1 : commV P ≤ W'.map (kOf ρ).subtype := by
        rw [← hK]
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨x, hx, rfl⟩
        exact hmem x hx
      exact hkOf.le.trans h1
    refine (Subgroup.eq_top_iff' _).2 fun k => ?_
    obtain ⟨w', hw', hwk⟩ := hKW k.2
    have : w' = k := Subtype.ext hwk
    rw [← this]
    exact hw'
  rcases class_aut hstr hfix hgenK with ⟨hp3, hc4⟩ | hbl
  · left
    refine ⟨hp3, ?_⟩
    rw [← card_map_eq_of_ker_eq hkb T0]
    exact hc4
  · right
    exact hbl

end Beta

end CFSG.Quasithin
