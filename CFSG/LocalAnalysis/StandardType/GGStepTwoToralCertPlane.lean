module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertCover

public section

namespace CFSG.StandardType.StepTwoToralCert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {p : ℕ}

@[simp] theorem tcEnv_p (L : List (Array ℤ)) (gens : Array (List ℕ)) :
    (tcEnv τ p L gens).p = p := rfl

@[simp] theorem tcEnv_n (L : List (Array ℤ)) (gens : Array (List ℕ)) :
    (tcEnv τ p L gens).n = τ.rank := rfl

@[simp] theorem tcEnv_L (L : List (Array ℤ)) (gens : Array (List ℕ)) :
    (tcEnv τ p L gens).L = L := rfl

@[simp] theorem tcEnv_gens (L : List (Array ℤ)) (gens : Array (List ℕ)) :
    (tcEnv τ p L gens).gens = gens := rfl

@[simp] theorem tcEnv_R (L : List (Array ℤ)) (gens : Array (List ℕ)) :
    (tcEnv τ p L gens).R = tcRoots τ () := rfl

theorem tcInV_iff (E : TcEnv) (v : Array ℤ) :
    tcInV E v = true ↔ tcVec E.p E.n v ∈ tcKerSub E.p E.n E.L := by
  simp only [tcInV, List.all_eq_true, beq_iff_eq, mem_tcKerSub]
  exact forall₂_congr fun r _ => tcDot_mod_eq_zero_iff r v

theorem tcInV_congr (E : TcEnv) {a b : Array ℤ} (h : tcVec E.p E.n a = tcVec E.p E.n b) :
    tcInV E a = tcInV E b := by
  rw [Bool.eq_iff_iff, tcInV_iff, tcInV_iff, h]

@[expose] def tcCanon (p n : ℕ) (d : Fin n → ZMod p) : Array ℤ :=
  Array.ofFn fun i => (((d i).val : ℕ) : ℤ)

theorem tcVec_tcCanon (hp : p.Prime) {n : ℕ} (d : Fin n → ZMod p) :
    tcVec p n (tcCanon p n d) = d := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [tcCanon, tcVec_ofFn]
  funext i
  simp

section Weyl


theorem tcGen_cast (L : List (Array ℤ)) (gens : Array (List ℕ)) (w : List ℕ) (f : Array ℤ) :
    tcVec p τ.rank (tcGenApply (tcEnv τ p L gens) w f) =
      cowAct (tcGenWordElt τ gens w) (tcVec p τ.rank f) :=
  tcGenWord_cast gens w f

theorem tcOrb_conj (hp : 0 < p) (L : List (Array ℤ)) (gens : Array (List ℕ)) {T : TcOrb}
    (hT : tcOrbOK (tcEnv τ p L gens) T = true) {v : Array ℤ}
    (hv : tcInV (tcEnv τ p L gens) v = true) :
    ∃ w : List ℕ, cowAct (tcGenWordElt τ gens w) (tcVec p τ.rank v) =
      tcVec p τ.rank (tcDec p τ.rank (T.rep.getD (tcEnc p τ.rank v) 0)) := by
  simp only [tcOrbOK, tcEnv_p, tcEnv_n, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hT
  have h1 := hT (tcEnc p τ.rank v) (tcEnc_lt hp v)
  have hv' : tcInV (tcEnv τ p L gens) (tcDec p τ.rank (tcEnc p τ.rank v)) = true := by
    have h3 : tcInV (tcEnv τ p L gens) (tcDec p τ.rank (tcEnc p τ.rank v)) =
        tcInV (tcEnv τ p L gens) v :=
      tcInV_congr (tcEnv τ p L gens) (a := tcDec p τ.rank (tcEnc p τ.rank v)) (b := v)
        (tcVec_tcDec_tcEnc hp v)
    rw [h3]
    exact hv
  rcases h1 with h1 | h1
  · rw [hv'] at h1
    exact absurd h1 (by simp)
  · refine ⟨T.word.getD (tcEnc p τ.rank v) [], ?_⟩
    have h2 := tcEqMod_iff.mp h1
    rw [tcGen_cast] at h2
    rw [tcVec_tcDec_tcEnc hp v] at h2
    exact h2

end Weyl

theorem tcLeadFrom_eq (a : Array ℤ) (k : ℕ) :
    ∀ s m : ℕ, s ≤ m → m < s + k → (∀ j, s ≤ j → j < m → tcEnt a j % (p : ℤ) = 0) →
      tcEnt a m % (p : ℤ) ≠ 0 → tcLeadFrom p a s k = m := by
  induction k with
  | zero => intro s m _ hm; omega
  | succ k ih =>
    intro s m hsm hm hz hnz
    simp only [tcLeadFrom]
    by_cases hs : tcEnt a s % (p : ℤ) = 0
    · have hne : s ≠ m := fun h => hnz (h ▸ hs)
      simp only [hs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      exact ih (s + 1) m (by omega) (by omega) (fun j hj1 hj2 => hz j (by omega) hj2) hnz
    · have : s = m := by
        by_contra hne
        exact hs (hz s le_rfl (by omega))
      simp only [bne_iff_ne, ne_eq, hs, not_false_eq_true, ↓reduceIte]
      exact this

theorem tcNormalized_of_first (hp : p.Prime) {n : ℕ} {a : Array ℤ} {d : Fin n → ZMod p}
    (hd : tcVec p n a = d) (k : Fin n) (h1 : d k = 1) (hz : ∀ j : Fin n, j < k → d j = 0) :
    tcNormalized p n a = true := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlead : tcLead p n a = k := by
    apply tcLeadFrom_eq a n 0 k (Nat.zero_le _) (by simpa using k.2)
    · intro j _ hj
      have := congrFun hd ⟨j, by omega⟩
      simp only [tcVec] at this
      rw [hz ⟨j, by omega⟩ (by simpa [Fin.lt_def] using hj)] at this
      exact intCast_eq_zero_iff'.mp this
    · have := congrFun hd k
      simp only [tcVec] at this
      rw [h1] at this
      exact intCast_ne_zero_iff.mp (by rw [this]; exact one_ne_zero)
  have hent : tcEnt a k % (p : ℤ) = 1 := by
    have := congrFun hd k
    simp only [tcVec] at this
    rw [h1] at this
    have h2 : tcEnt a k % (p : ℤ) = 1 % (p : ℤ) :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mp (this.trans (Int.cast_one).symm)
    rw [h2]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hp.one_lt)
  simp only [tcNormalized, hlead, hent]
  rfl

theorem exists_first_ne_zero {F : Type*} [Zero F] {n : ℕ} (f : Fin n → F) (hf : f ≠ 0) :
    ∃ k : Fin n, f k ≠ 0 ∧ ∀ j : Fin n, j < k → f j = 0 := by
  by_contra hcon
  push Not at hcon
  apply hf
  funext i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    by_contra hne
    obtain ⟨j, hj, hjne⟩ := hcon i hne
    exact hjne (ih j hj)

theorem tcVec_tcComb2 {n : ℕ} (a b : ℕ) (d1 d2 : Array ℤ) :
    tcVec p n (tcComb2 n a b d1 d2) =
      (a : ZMod p) • tcVec p n d1 + (b : ZMod p) • tcVec p n d2 := by
  funext i
  simp [tcVec, tcComb2, tcEnt_ofFn]

section Plane


@[expose] def TcHit (π : Equiv.Perm (Fin τ.rank)) (basis : List (Array ℤ))
    (d : Fin τ.rank → ZMod p) : Prop :=
  ∃ s ∈ Submodule.span (ZMod p) {f | ∃ g ∈ basis, f = tcVec p τ.rank g}, s ≠ 0 ∧
    ∃ u : WeylGroup τ, CommutesPi π u ∧ cowAct u s = d

theorem tcHit_of_rep_eq (hp : 0 < p) {L : List (Array ℤ)} {gens : Array (List ℕ)} {T : TcOrb}
    (hT : tcOrbOK (tcEnv τ p L gens) T = true) {π : Equiv.Perm (Fin τ.rank)}
    (hgens : ∀ gi, CommutesPi π (tcWordElt τ (gens.getD gi []))) {basis : List (Array ℤ)}
    {s v : Array ℤ} (hs : tcInV (tcEnv τ p L gens) s = true)
    (hsS : tcVec p τ.rank s ∈ Submodule.span (ZMod p) {f | ∃ g ∈ basis, f = tcVec p τ.rank g})
    (hsne : tcVec p τ.rank s ≠ 0) (hv : tcInV (tcEnv τ p L gens) v = true)
    (hrep : T.rep.getD (tcEnc p τ.rank s) 0 = T.rep.getD (tcEnc p τ.rank v) 0) :
    TcHit π basis (tcVec p τ.rank v) := by
  obtain ⟨ws, hws⟩ := tcOrb_conj hp L gens hT hs
  obtain ⟨wv, hwv⟩ := tcOrb_conj hp L gens hT hv
  rw [hrep] at hws
  refine ⟨tcVec p τ.rank s, hsS, hsne, (tcGenWordElt τ gens wv)⁻¹ * tcGenWordElt τ gens ws,
    commutesPi_mul (commutesPi_inv (commutesPi_genWordElt hgens wv))
      (commutesPi_genWordElt hgens ws), ?_⟩
  rw [cowAct_mul, hws, ← hwv, cowAct_inv_cowAct]

theorem tcNTable_getD (E : TcEnv) (T : TcOrb) (basis : List (Array ℤ)) {idx : ℕ}
    (hidx : idx < E.p ^ E.n) :
    (tcNTable E T basis).getD idx false =
      (tcInV E (tcDec E.p E.n idx) && !tcIsZero E.p E.n (tcDec E.p E.n idx) &&
        !(tcHitReps E T basis).contains (T.rep.getD idx 0)) := by
  simp [tcNTable, Array.getD_eq_getD_getElem?, hidx]

theorem tcNTable_of_not_hit (hp : p.Prime) {L : List (Array ℤ)} {gens : Array (List ℕ)}
    {T : TcOrb} (hT : tcOrbOK (tcEnv τ p L gens) T = true) {π : Equiv.Perm (Fin τ.rank)}
    (hgens : ∀ gi, CommutesPi π (tcWordElt τ (gens.getD gi []))) {basis : List (Array ℤ)}
    (hbasis : ∀ g ∈ basis, tcInV (tcEnv τ p L gens) g = true)
    {d : Fin τ.rank → ZMod p} (hdV : d ∈ tcKerSub p τ.rank L) (hd0 : d ≠ 0)
    (hnh : ¬ TcHit π basis d) :
    (tcNTable (tcEnv τ p L gens) T basis).getD (tcEnc p τ.rank (tcCanon p τ.rank d)) false =
      true := by
  have hidx : tcEnc p τ.rank (tcCanon p τ.rank d) < (tcEnv τ p L gens).p ^
      (tcEnv τ p L gens).n := tcEnc_lt hp.pos _
  rw [tcNTable_getD _ _ _ hidx]
  simp only [tcEnv_p, tcEnv_n]
  have hvec : tcVec p τ.rank (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank d))) = d := by
    rw [tcVec_tcDec_tcEnc hp.pos, tcVec_tcCanon hp]
  have hV1 : tcInV (tcEnv τ p L gens)
      (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank d))) = true := by
    rw [tcInV_iff]
    show tcVec p τ.rank _ ∈ tcKerSub p τ.rank L
    rw [hvec]
    exact hdV
  have hz : tcIsZero p τ.rank (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank d))) = false := by
    by_contra hcon
    have h1 : tcIsZero p τ.rank
        (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank d))) = true := by simpa using hcon
    rw [tcIsZero_iff, hvec] at h1
    exact hd0 h1
  have hc : (tcHitReps (tcEnv τ p L gens) T basis).contains
      (T.rep.getD (tcEnc p τ.rank (tcCanon p τ.rank d)) 0) = false := by
    by_contra hcon
    have h1 : (tcHitReps (tcEnv τ p L gens) T basis).contains
        (T.rep.getD (tcEnc p τ.rank (tcCanon p τ.rank d)) 0) = true := by simpa using hcon
    rw [List.contains_iff_mem] at h1
    simp only [tcHitReps, tcEnv_p, tcEnv_n, List.mem_dedup, List.mem_map, tcCombos,
      List.mem_filter, List.mem_range, Bool.not_eq_true'] at h1
    obtain ⟨s, ⟨⟨t, -, rfl⟩, hsz⟩, hrep⟩ := h1
    have hsS := tcCombo_mem (p := p) (n := τ.rank) basis t
    have hSV : Submodule.span (ZMod p) {f | ∃ g ∈ basis, f = tcVec p τ.rank g} ≤
        tcKerSub p τ.rank L := by
      refine Submodule.span_le.mpr ?_
      rintro f ⟨g, hg, rfl⟩
      exact (tcInV_iff _ g).mp (hbasis g hg)
    have hs : tcInV (tcEnv τ p L gens) (tcCombo p τ.rank basis t) = true := by
      rw [tcInV_iff]
      exact hSV hsS
    have hv : tcInV (tcEnv τ p L gens) (tcCanon p τ.rank d) = true := by
      rw [tcInV_iff]
      show tcVec p τ.rank _ ∈ tcKerSub p τ.rank L
      rw [tcVec_tcCanon hp]
      exact hdV
    apply hnh
    have := tcHit_of_rep_eq hp.pos hT hgens (basis := basis) (s := tcCombo p τ.rank basis t)
      (v := tcCanon p τ.rank d) hs hsS (tcCombo_ne_zero hsz) hv hrep
    rwa [tcVec_tcCanon hp] at this
  rw [hV1, hz, hc]
  rfl

theorem tcDot_root_mod_iff {i : ℕ} (hi : i < τ.rootCertificate.roots.length) (a : Array ℤ) :
    tcDot τ.rank ((tcRoots τ ()).getD i #[]) a % (p : ℤ) = 0 ↔
      latChar p (tcVec p τ.rank a) (τ.rootCertificate.root i) = 0 := by
  rw [tcRoots_getD τ hi, tcDot_mod_eq_zero_iff, tcFun_ofFn]

theorem mem_tcPhi2_iff (a1 a2 : Array ℤ) (i : ℕ) :
    i ∈ (List.range (tcRoots τ ()).size).filter (fun r =>
        tcDot τ.rank ((tcRoots τ ()).getD r #[]) a1 % (p : ℤ) == 0 &&
          tcDot τ.rank ((tcRoots τ ()).getD r #[]) a2 % (p : ℤ) == 0) ↔
      i < τ.rootCertificate.roots.length ∧
        latChar p (tcVec p τ.rank a1) (τ.rootCertificate.root i) = 0 ∧
          latChar p (tcVec p τ.rank a2) (τ.rootCertificate.root i) = 0 := by
  rw [List.mem_filter, List.mem_range, tcRoots_size, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro ⟨hi, h1, h2⟩
    exact ⟨hi, (tcDot_root_mod_iff hi a1).mp h1, (tcDot_root_mod_iff hi a2).mp h2⟩
  · rintro ⟨hi, h1, h2⟩
    exact ⟨hi, (tcDot_root_mod_iff hi a1).mpr h1, (tcDot_root_mod_iff hi a2).mpr h2⟩

theorem tcPlane_ker_le {a1 a2 : Array ℤ}
    {D : Submodule (ZMod p) (Fin τ.rank → ZMod p)} (ha1 : tcVec p τ.rank a1 ∈ D)
    (ha2 : tcVec p τ.rank a2 ∈ D) {phi : List ℕ}
    (hphi : ∀ i, i ∈ phi ↔ i < τ.rootCertificate.roots.length ∧
      latChar p (tcVec p τ.rank a1) (τ.rootCertificate.root i) = 0 ∧
        latChar p (tcVec p τ.rank a2) (τ.rootCertificate.root i) = 0) :
    annSub p (tcRootSet τ phi) ≤ annSub p (phiSet p (D : Set (Fin τ.rank → ZMod p))) := by
  intro f hf α hα
  obtain ⟨hα1, hα2⟩ := hα
  obtain ⟨i, hi, rfl⟩ := isRoot_iff_exists_index.mp hα1
  exact hf _ ⟨i, (hphi i).mpr ⟨hi, hα2 _ ha1, hα2 _ ha2⟩, hi, rfl⟩

theorem tcPlaneOK_sound (hp : p.Prime) {L : List (Array ℤ)} {gens : Array (List ℕ)} {T : TcOrb}
    (hT : tcOrbOK (tcEnv τ p L gens) T = true) {π : Equiv.Perm (Fin τ.rank)}
    (hgens : ∀ gi, CommutesPi π (tcWordElt τ (gens.getD gi []))) {basis : List (Array ℤ)}
    (hbasis : ∀ g ∈ basis, tcInV (tcEnv τ p L gens) g = true)
    (h : tcPlaneOK (tcEnv τ p L gens) T basis = true)
    {D : Submodule (ZMod p) (Fin τ.rank → ZMod p)} (hD : QualPlane p (tcKerSub p τ.rank L) D) :
    ∃ d ∈ D, d ≠ 0 ∧ TcHit π basis d := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hnone
  push Not at hnone
  obtain ⟨hDV, hDcard, hphi, hker⟩ := hD
  have hfin : Module.finrank (ZMod p) D = 2 := finrank_eq_two_of_natCard hp D hDcard
  obtain ⟨d1, hd1, hd10, d2, hd2, hind⟩ := tcExists_two_independent hp D hfin
  obtain ⟨k, hk0, hkmin⟩ := exists_first_ne_zero d1 hd10
  have hd1'D : (d1 k)⁻¹ • d1 ∈ D := D.smul_mem _ hd1
  have hd1'k : ((d1 k)⁻¹ • d1) k = 1 := by simp [hk0]
  have hd1'min : ∀ j : Fin τ.rank, j < k → ((d1 k)⁻¹ • d1) j = 0 := by
    intro j hj
    simp [hkmin j hj]
  have hd1'0 : (d1 k)⁻¹ • d1 ≠ 0 := fun h0 => by
    have := congrFun h0 k
    simp [hk0] at this
  have hind' : ∀ c : ZMod p, d2 ≠ c • ((d1 k)⁻¹ • d1) := fun c hc =>
    hind (c * (d1 k)⁻¹) (by rw [hc, smul_smul])
  have hd20 : d2 ≠ 0 := fun h0 => hind 0 (by rw [h0, zero_smul])
  generalize (d1 k)⁻¹ • d1 = e1 at hd1'D hd1'k hd1'min hd1'0 hind'
  have hnt : ∀ x ∈ D, x ≠ 0 → (tcNTable (tcEnv τ p L gens) T basis).getD
      (tcEnc p τ.rank (tcCanon p τ.rank x)) false = true := fun x hx hx0 =>
    tcNTable_of_not_hit hp hT hgens hbasis (hDV hx) hx0 (hnone x hx hx0)
  simp only [tcPlaneOK, tcEnv_p, tcEnv_n, List.all_eq_true, List.mem_filter, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  have hv1 : ∀ x : Fin τ.rank → ZMod p,
      tcVec p τ.rank (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank x))) = x := fun x => by
    rw [tcVec_tcDec_tcEnc hp.pos, tcVec_tcCanon hp]
  have hnorm : tcNormalized p τ.rank
      (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank e1))) = true :=
    tcNormalized_of_first hp (hv1 e1) k hd1'k hd1'min
  rcases h (tcEnc p τ.rank (tcCanon p τ.rank e1))
      ⟨tcEnc_lt hp.pos _, hnt e1 hd1'D hd1'0⟩ with h1 | h1
  · rw [hnorm] at h1
    exact absurd h1 (by decide)
  have hin : tcPlaneIn p τ.rank (tcNTable (tcEnv τ p L gens) T basis)
      (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank e1)))
      (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank d2))) = true := by
    simp only [tcPlaneIn, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
      Bool.or_eq_true, beq_iff_eq]
    refine ⟨fun c _ => ?_, fun a ha b hb => ?_⟩
    · by_contra hcon
      have hc' := tcEqMod_iff.mp (by simpa using hcon)
      rw [tcVec_tcComb2, hv1, hv1] at hc'
      exact hind' (c : ZMod p) (by simpa using hc')
    · by_cases hab : a = 0 ∧ b = 0
      · exact Or.inl hab
      · right
        have hxD : (a : ZMod p) • e1 + (b : ZMod p) • d2 ∈ D :=
          D.add_mem (D.smul_mem _ hd1'D) (D.smul_mem _ hd2)
        have hx0 : (a : ZMod p) • e1 + (b : ZMod p) • d2 ≠ 0 := by
          intro hx
          by_cases hb0 : (b : ZMod p) = 0
          · rw [hb0, zero_smul, add_zero, smul_eq_zero] at hx
            rcases hx with ha0 | he1
            · apply hab
              refine ⟨?_, ?_⟩
              · exact Nat.eq_zero_of_dvd_of_lt
                  ((ZMod.natCast_eq_zero_iff a p).mp ha0) ha
              · exact Nat.eq_zero_of_dvd_of_lt
                  ((ZMod.natCast_eq_zero_iff b p).mp hb0) hb
            · exact hd1'0 he1
          · apply hind' (-((a : ZMod p) * (b : ZMod p)⁻¹))
            funext j
            have h3j := congrFun hx j
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h3j ⊢
            field_simp
            linear_combination h3j
        have hcongr : tcEnc p τ.rank (tcComb2 τ.rank a b
            (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank e1)))
            (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank d2)))) =
            tcEnc p τ.rank (tcCanon p τ.rank ((a : ZMod p) • e1 + (b : ZMod p) • d2)) :=
          tcEnc_congr (by rw [tcVec_tcComb2, hv1, hv1, tcVec_tcCanon hp])
        rw [hcongr]
        exact hnt _ hxD hx0
  rcases h1 (tcEnc p τ.rank (tcCanon p τ.rank d2)) ⟨tcEnc_lt hp.pos _, hnt d2 hd2 hd20⟩
    with h2 | h2
  · rw [hin] at h2
    exact absurd h2 (by decide)
  · simp only [tcPlaneBad, tcEnv_p, tcEnv_n, tcEnv_R, tcEnv_L, Bool.or_eq_true,
      List.isEmpty_iff, Bool.and_eq_true] at h2
    rcases h2 with hempty | ⟨hlen, hkerok⟩
    · obtain ⟨α, hα1, hα2⟩ := hphi
      obtain ⟨i, hi, rfl⟩ := isRoot_iff_exists_index.mp hα1
      have hmem := (mem_tcPhi2_iff (p := p) (τ := τ)
        (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank e1)))
        (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank d2))) i).mpr
        ⟨hi, by rw [hv1]; exact hα2 e1 hd1'D, by rw [hv1]; exact hα2 d2 hd2⟩
      rw [hempty] at hmem
      simp at hmem
    · have h4 := tcKerOK_finrank_ge hp hkerok
      rw [List.length_take, min_eq_left (of_decide_eq_true hlen), tcKerSub_rows_eq] at h4
      have hle := tcPlane_ker_le (p := p) (τ := τ) (D := D)
        (by rw [hv1]; exact hd1'D) (by rw [hv1]; exact hd2)
        (mem_tcPhi2_iff (p := p) (τ := τ)
          (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank e1)))
          (tcDec p τ.rank (tcEnc p τ.rank (tcCanon p τ.rank d2))))
      have h5 : 4 ≤ Module.finrank (ZMod p)
          ↥(tcKerSub p τ.rank L ⊓ annSub p (phiSet p (D : Set (Fin τ.rank → ZMod p)))) :=
        h4.trans (finrank_mono_zmod hp (inf_le_inf_left _ hle))
      have h6 := natCard_ge_pow hp _ h5
      have h7 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega

end Plane

end CFSG.StandardType.StepTwoToralCert
