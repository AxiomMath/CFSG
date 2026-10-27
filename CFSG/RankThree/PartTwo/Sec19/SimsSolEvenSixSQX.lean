module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSFusion
public import CFSG.RankThree.Transfer.WeaklyClosed

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace SixSQXAux

variable {H : Type*} [Group H]

theorem exists_hom_ne_one_of_mul_self_mem (N : Subgroup H) (hsq : ∀ m : H, m * m ∈ N) {g : H}
    (hg : g ∉ N) : ∃ φ : H →* Multiplicative (ZMod 2), φ g ≠ 1 := by
  haveI : N.Normal := ⟨fun n hn m => by
    have e : m * n * m⁻¹ = m * n * (m * n) * n⁻¹ * (m⁻¹ * m⁻¹) := by group
    rw [e]
    exact N.mul_mem (N.mul_mem (hsq _) (N.inv_mem hn)) (hsq _)⟩
  have hE2 : ∀ e : H ⧸ N, e * e = 1 := fun e => by
    induction e using QuotientGroup.induction_on with
    | H m => rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]; exact hsq m
  have hinv : ∀ e : H ⧸ N, e⁻¹ = e := fun e => inv_eq_of_mul_eq_one_right (hE2 e)
  letI : CommGroup (H ⧸ N) :=
    { (inferInstance : Group (H ⧸ N)) with
      mul_comm := fun a b => by
        calc a * b = (a * b)⁻¹ := (hinv _).symm
          _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
          _ = b * a := by rw [hinv, hinv] }
  letI : Module (ZMod 2) (Additive (H ⧸ N)) :=
    AddCommGroup.zmodModule fun x => by
      rw [two_nsmul]
      exact hE2 (Additive.toMul x)
  have hne : Additive.ofMul (g : H ⧸ N) ≠ 0 := fun h => hg ((QuotientGroup.eq_one_iff g).1 h)
  obtain ⟨f, hf⟩ := not_forall.1
    (mt (Module.forall_dual_apply_eq_zero_iff (ZMod 2) (Additive.ofMul (g : H ⧸ N))).1 hne)
  refine ⟨(AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom).comp (QuotientGroup.mk' N), ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    AddMonoidHom.toMultiplicativeRight_apply_apply, Ne, ofAdd_eq_one]
  exact hf

theorem hom_eq_one_of_isSimpleGroup {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (μ : G →* Multiplicative (ZMod 2)) : μ = 1 := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal μ.ker with h | h
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd ((MonoidHom.ker_eq_bot_iff μ).1 h (by rw [map_mul, map_mul, mul_comm])) hab
  · exact MonoidHom.ker_eq_top_iff.1 h

variable {X Q K : Subgroup H} {t : H}

theorem twist_mem (hKn : ∀ h : H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (ht2 : t * t = 1) {q : H}
    (hq : q ∈ K) : q * t * q * t ∈ K := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have h1 : t * q * t ∈ K := by simpa [ht] using hKn t q hq
  simpa [mul_assoc] using K.mul_mem hq h1

theorem twist_mul (hQn : ∀ h : H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (ht2 : t * t = 1) {q q' : H} (hq : q ∈ Q)
    (hq' : q' ∈ Q) : q * q' * t * (q * q') * t = q * t * q * t * (q' * t * q' * t) := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htt : ∀ x : H, t * (t * x) = x := fun x => by rw [← mul_assoc, ht2, one_mul]
  have ha : t * q * t ∈ Q := by simpa [ht] using hQn t q hq
  have e : q * q' * t * (q * q') * t = q * (q' * (t * q * t)) * (t * q' * t) := by
    simp only [mul_assoc, htt]
  rw [e, hQab q' hq' _ ha]
  simp only [mul_assoc]

theorem twist_twist (hQ2 : ∀ q ∈ Q, q * q = 1) (ht2 : t * t = 1) {q : H} (hq : q ∈ Q) :
    q * t * q * t * t * (q * t * q * t) * t = 1 := by
  have htt : ∀ x : H, t * (t * x) = x := fun x => by rw [← mul_assoc, ht2, one_mul]
  have hqq : ∀ x : H, q * (q * x) = x := fun x => by rw [← mul_assoc, hQ2 q hq, one_mul]
  simp only [mul_assoc, htt, hqq, ht2, hQ2 q hq, mul_one]

theorem exists_twist_subgroup (hXn : ∀ h : H, ∀ y ∈ X, h * y * h⁻¹ ∈ X)
    (hQn : ∀ h : H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hQ2 : ∀ q ∈ Q, q * q = 1) (ht2 : t * t = 1) :
    ∃ N : Subgroup H, ∀ m, m ∈ N ↔ ∃ q ∈ Q, ∃ y ∈ X, m = q * t * q * t * y := by
  refine ⟨{ carrier := {m | ∃ q ∈ Q, ∃ y ∈ X, m = q * t * q * t * y}
            one_mem' := ?one
            mul_mem' := ?mul
            inv_mem' := ?inv }, fun m => Iff.rfl⟩
  case one => exact ⟨1, Q.one_mem, 1, X.one_mem, by simp [ht2]⟩
  case mul =>
    rintro _ _ ⟨q, hq, y, hy, rfl⟩ ⟨q', hq', y', hy', rfl⟩
    refine ⟨q * q', Q.mul_mem hq hq', (q' * t * q' * t)⁻¹ * y * (q' * t * q' * t) * y',
      X.mul_mem ?_ hy', ?_⟩
    · simpa using hXn (q' * t * q' * t)⁻¹ y hy
    · rw [twist_mul hQn hQab ht2 hq hq']
      group
  case inv =>
    rintro _ ⟨q, hq, y, hy, rfl⟩
    have hcc := hQ2 _ (twist_mem hQn ht2 hq)
    refine ⟨q, hq, q * t * q * t * y⁻¹ * (q * t * q * t)⁻¹, hXn _ _ (X.inv_mem hy), ?_⟩
    calc (q * t * q * t * y)⁻¹
        = q * t * q * t * (q * t * q * t) * y⁻¹ * (q * t * q * t)⁻¹ := by
          rw [hcc, one_mul]
          group
      _ = q * t * q * t * (q * t * q * t * y⁻¹ * (q * t * q * t)⁻¹) := by group

theorem mul_self_eq_twist (hXn : ∀ h : H, ∀ y ∈ X, h * y * h⁻¹ ∈ X)
    (hQn : ∀ h : H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) (hQ2 : ∀ q ∈ Q, q * q = 1) (ht2 : t * t = 1)
    (hdec : ∀ m : H, ∃ q ∈ Q, ∃ y ∈ X, m = q * y ∨ m = q * y * t) (m : H) :
    ∃ q ∈ Q, ∃ y ∈ X, m * m = q * t * q * t * y := by
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htt : ∀ x : H, t * (t * x) = x := fun x => by rw [← mul_assoc, ht2, one_mul]
  obtain ⟨q, hq, y, hy, h | h⟩ := hdec m
  · have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_right (hQ2 q hq)
    refine ⟨1, Q.one_mem, q * y * q⁻¹ * y, X.mul_mem (hXn q y hy) hy, ?_⟩
    rw [h, hq']
    simp only [mul_one, one_mul, mul_assoc, htt]
  · have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_right (hQ2 q hq)
    have hqq : ∀ x : H, q * (q * x) = x := fun x => by rw [← mul_assoc, hQ2 q hq, one_mul]
    have hty : t * y * t ∈ X := by simpa [ht] using hXn t y hy
    refine ⟨q, hq, t * q * t * y * (t * q * t)⁻¹ * (t * y * t),
      X.mul_mem (hXn _ y hy) hty, ?_⟩
    rw [h]
    simp only [mul_inv_rev, ht, hq', mul_assoc, htt, hqq]

end SixSQXAux

theorem le_of_forall_hom_eq_one {H : Type*} [Group H] [Finite H] {X Q : Subgroup H}
    (hXn : ∀ h : H, ∀ y ∈ X, h * y * h⁻¹ ∈ X) (hQn : ∀ h : H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hQ2 : ∀ q ∈ Q, q * q = 1) {t : H}
    (ht2 : t * t = 1) (hdec : ∀ m : H, ∃ q ∈ Q, ∃ y ∈ X, m = q * y ∨ m = q * y * t)
    (hφ : ∀ φ : H →* Multiplicative (ZMod 2), ∀ q ∈ Q, φ q = 1) : Q ≤ X := by
  obtain ⟨N, hN⟩ := SixSQXAux.exists_twist_subgroup hXn hQn hQab hQ2 ht2
  have hsq : ∀ m : H, m * m ∈ N := fun m =>
    (hN _).2 (SixSQXAux.mul_self_eq_twist hXn hQn hQ2 ht2 hdec m)
  have hQN : Q ≤ N := fun q hq => by
    by_contra hqN
    obtain ⟨φ, hφq⟩ := SixSQXAux.exists_hom_ne_one_of_mul_self_mem N hsq hqN
    exact hφq (hφ φ q hq)
  have hdecQ : ∀ q ∈ Q, ∃ q₁ ∈ Q, ∃ y ∈ X, y ∈ Q ∧ q = q₁ * t * q₁ * t * y := fun q hq => by
    obtain ⟨q₁, hq₁, y, hy, rfl⟩ := (hN q).1 (hQN hq)
    refine ⟨q₁, hq₁, y, hy, ?_, rfl⟩
    have h := Q.mul_mem (Q.inv_mem (SixSQXAux.twist_mem hQn ht2 hq₁)) hq
    rwa [inv_mul_cancel_left] at h
  intro q hq
  obtain ⟨q₁, hq₁, y₁, hy₁, -, rfl⟩ := hdecQ q hq
  obtain ⟨q₂, hq₂, y₂, hy₂, hy₂Q, rfl⟩ := hdecQ q₁ hq₁
  refine X.mul_mem ?_ hy₁
  rw [SixSQXAux.twist_mul hQn hQab ht2 (SixSQXAux.twist_mem hQn ht2 hq₂) hy₂Q,
    SixSQXAux.twist_twist hQ2 ht2 hq₂, one_mul]
  exact SixSQXAux.twist_mem hXn ht2 hy₂

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

include D in
theorem exists_sylow_weaklyClosed (hR2 : Nat.card ↥(Rc X) = 2)
    (hsurj : Function.Surjective C.θ) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M ∧ CFSG.Open.pCoreOf 2 M ≤ S ∧
      ∀ g : G, conjSubgroup g (CFSG.Open.pCoreOf 2 M) ≤ S →
        conjSubgroup g (CFSG.Open.pCoreOf 2 M) = CFSG.Open.pCoreOf 2 M := by
  obtain ⟨S, hSM⟩ := exists_sylow_le_M (C := C) hR2 hsurj
  have hR : Nat.card ↥(Rc X) ≤ 2 := hR2.le
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQ
  have hQS : Q ≤ (S : Subgroup G) := by
    have hN : (S : Subgroup G) ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
      rw [C.S.normalizer_Q_eq]
      exact hSM
    have h2 : IsPGroup 2 (Q ⊔ (S : Subgroup G) : Subgroup G) :=
      (isPGroup_pCoreOf' M).to_sup_of_normal_left' S.isPGroup' hN
    rw [← S.is_maximal' h2 le_sup_right]
    exact le_sup_left
  refine ⟨S, hSM, hQS, fun g hg => ?_⟩
  have hRb : Rc X ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hR2
    norm_num at hR2
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRb
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrQ : r ∈ Q := by
    have h := hr
    rw [C.S.R_eq_inf] at h
    exact (Subgroup.mem_inf.1 h).1
  have hconj : g⁻¹ * r * g ∈ Q := by
    have hCQ := C.centralizer_Q_eq hR
    rw [← hQ] at hCQ
    rw [← hCQ, Subgroup.mem_centralizer_iff]
    intro q hq
    have hgq : g * q * g⁻¹ ∈ conjSubgroup g Q :=
      mem_conjSubgroup.2 (by simpa [mul_assoc] using hq)
    have hgqM : g * q * g⁻¹ ∈ M := hSM (hg hgq)
    have hc := mul_inv_eq_iff_eq_mul.1 (C.S.R_central hR hgqM hr)
    calc q * (g⁻¹ * r * g) = g⁻¹ * ((g * q * g⁻¹) * r) * g := by group
      _ = g⁻¹ * (r * (g * q * g⁻¹)) * g := by rw [hc]
      _ = (g⁻¹ * r * g) * q := by group
  have hl : barLen (Multiplicative.toAdd (D.piQ ⟨r, hrQ⟩)) ≠ 2 := by
    rw [(D.piQ_eq_one_iff ⟨r, hrQ⟩).2 hr, toAdd_one, H4b.barLen_zero']
    norm_num
  have hgM := D.mem_M_of_conj_len_ne_two hR hsurj hrQ hr1' hl (g := g⁻¹) (by simpa using hconj)
  exact TI.conj_eq_of_mem_M (by simpa using M.inv_mem hgM)

include D in
theorem hom_apply_eq_one (hR2 : Nat.card ↥(Rc X) = 2) (hsurj : Function.Surjective C.θ)
    (hel : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * q = 1) (φ : ↥M →* Multiplicative (ZMod 2)) {q : G}
    (hq : q ∈ CFSG.Open.pCoreOf 2 M) : φ ⟨q, pCoreOf_le_self M hq⟩ = 1 := by
  obtain ⟨S, hSM, hQS, hwc⟩ := D.exists_sylow_weaklyClosed hR2 hsurj
  have hNM := C.S.normalizer_Q_eq
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) := by
    rw [hNM]
    exact hSM
  exact CFSG.RankThree.Transfer.apply_eq_one_of_weaklyClosed S hQS hSN hwc (C.Q_comm hR2.le) hel
    (SixSQXAux.hom_eq_one_of_isSimpleGroup C.S.simple C.S.nonab)
    (φ.comp (MulEquiv.subgroupCongr hNM).toMonoidHom) hq

include D in
theorem Q_le_X (hR2 : Nat.card ↥(Rc X) = 2) (hsurj : Function.Surjective C.θ)
    (hel : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * q = 1) (t : ↥M) (ht2 : (t : G) * t = 1)
    (hodd : Equiv.Perm.sign (C.θ t) = -1) : CFSG.Open.pCoreOf 2 M ≤ X := by
  have hR : Nat.card ↥(Rc X) ≤ 2 := hR2.le
  have ht2' : t * t = 1 := Subtype.ext ht2
  have hker := C.theta_ker_eq hR
  have heven : ∀ m : ↥M, Equiv.Perm.sign (C.θ m) = 1 →
      ∃ q ∈ (CFSG.Open.pCoreOf 2 M).subgroupOf M, ∃ y ∈ X.subgroupOf M, m = q * y := by
    intro m hm
    obtain ⟨x, hx⟩ := C.exists_lift (Equiv.Perm.mem_alternatingGroup.2 hm)
    refine ⟨m * ⟨x, C.S.le x.2⟩⁻¹, ?_, ⟨x, C.S.le x.2⟩, x.2, by group⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel]
  have hdec : ∀ m : ↥M, ∃ q ∈ (CFSG.Open.pCoreOf 2 M).subgroupOf M, ∃ y ∈ X.subgroupOf M,
      m = q * y ∨ m = q * y * t := by
    intro m
    rcases Int.units_eq_one_or (Equiv.Perm.sign (C.θ m)) with h | h
    · obtain ⟨q, hq, y, hy, e⟩ := heven m h
      exact ⟨q, hq, y, hy, Or.inl e⟩
    · obtain ⟨q, hq, y, hy, e⟩ := heven (m * t) (by rw [map_mul, map_mul, h, hodd]; decide)
      refine ⟨q, hq, y, hy, Or.inr ?_⟩
      rw [← e, mul_assoc, ht2', mul_one]
  have key := le_of_forall_hom_eq_one (X := X.subgroupOf M)
    (Q := (CFSG.Open.pCoreOf 2 M).subgroupOf M) (fun h y hy => C.S.normal h.2 hy)
    (fun h q hq => pCoreOf_normalized M h.2 hq)
    (fun a ha b hb => Subtype.ext (C.Q_comm hR _ ha _ hb)) (fun q hq => Subtype.ext (hel _ hq))
    ht2' hdec (fun φ q hq => D.hom_apply_eq_one hR2 hsurj hel φ hq)
  intro q hq
  exact key (show (⟨q, pCoreOf_le_self M hq⟩ : ↥M) ∈ (CFSG.Open.pCoreOf 2 M).subgroupOf M from hq)

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
