module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenAlt
public import CFSG.Open.Defs
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen

open Equiv Equiv.Perm Subgroup CFSG.Open

variable {K : Type} [Group K] [Finite K]

theorem card_sup_dvd_of_commute {A B : Subgroup K} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card (A ⊔ B : Subgroup K) ∣ Nat.card A * Nat.card B := by
  have hc : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b => hAB a a.2 b b.2
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hc).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact Subgroup.card_range_dvd _

theorem card_sup_of_commute {A B : Subgroup K} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup K) = Nat.card A * Nat.card B := by
  have hc : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b => hAB a a.2 b b.2
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hc).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hc) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [range_subtype, range_subtype, disjoint_iff]
    exact hinf
  rw [← hrange, ← Nat.card_prod]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem isElemAbelian_of_le_sup_of_commute {A B : Subgroup K}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : ∀ P : Subgroup K, P ≤ A → IsPGroup 3 P → IsElemAbelian 3 P)
    (hB : ∀ P : Subgroup K, P ≤ B → IsPGroup 3 P → IsElemAbelian 3 P) :
    ∀ P : Subgroup K, P ≤ A ⊔ B → IsPGroup 3 P → IsElemAbelian 3 P := by
  intro P hP hP3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b => hAB a a.2 b b.2
  set φ : A × B →* K := MonoidHom.noncommCoprod A.subtype B.subtype hc with hφ
  have hrange : φ.range = A ⊔ B := by
    rw [hφ, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  set D : Subgroup (A × B) := P.comap φ with hD
  set f : D →* P := (φ.comp D.subtype).codRestrict P (fun d => d.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ φ.range := by
      rw [hrange]
      exact hP hx
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hx'
    have hyD : y ∈ D := by
      change φ y ∈ P
      rw [hy]
      exact hx
    exact ⟨⟨y, hyD⟩, Subtype.ext hy⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 D) := inferInstance
  have hQtop : ((Sylow.mapSurjective hfs Q : Sylow 3 P) : Subgroup P) = ⊤ :=
    ((Sylow.mapSurjective hfs Q).3 (hP3.of_equiv Subgroup.topEquiv.symm) le_top).symm
  set Q' : Subgroup (A × B) := (Q : Subgroup D).map D.subtype with hQ'
  have hQ'3 : IsPGroup 3 Q' := Q.2.map D.subtype
  have hQA := hA ((Q'.map (MonoidHom.fst A B)).map A.subtype) (map_subtype_le _)
    ((hQ'3.map _).map _)
  have hQB := hB ((Q'.map (MonoidHom.snd A B)).map B.subtype) (map_subtype_le _)
    ((hQ'3.map _).map _)
  have hmA : ∀ q ∈ Q', (q.1 : K) ∈ (Q'.map (MonoidHom.fst A B)).map A.subtype := fun q hq =>
    mem_map_of_mem A.subtype (mem_map_of_mem (MonoidHom.fst A B) hq)
  have hmB : ∀ q ∈ Q', (q.2 : K) ∈ (Q'.map (MonoidHom.snd A B)).map B.subtype := fun q hq =>
    mem_map_of_mem B.subtype (mem_map_of_mem (MonoidHom.snd A B) hq)
  have hcomm : ∀ q₁ ∈ Q', ∀ q₂ ∈ Q', q₁ * q₂ = q₂ * q₁ := by
    intro q₁ h₁ q₂ h₂
    have ha := hQA.1.is_comm.comm ⟨_, hmA q₁ h₁⟩ ⟨_, hmA q₂ h₂⟩
    have hb := hQB.1.is_comm.comm ⟨_, hmB q₁ h₁⟩ ⟨_, hmB q₂ h₂⟩
    rw [Subtype.ext_iff] at ha hb
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hexp : ∀ q ∈ Q', q ^ 3 = 1 := by
    intro q hq
    have ha := hQA.2 _ (hmA q hq)
    have hb := hQB.2 _ (hmB q hq)
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simpa using ha
    · simpa using hb
  have hlift : ∀ x ∈ P, ∃ q ∈ Q', φ q = x := by
    intro x hx
    have hxt : (⟨x, hx⟩ : P) ∈ ((Sylow.mapSurjective hfs Q : Sylow 3 P) : Subgroup P) := by
      rw [hQtop]
      exact mem_top _
    rw [Sylow.coe_mapSurjective] at hxt
    obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.1 hxt
    rw [Subtype.ext_iff] at hdx
    exact ⟨d, mem_map_of_mem D.subtype hd, hdx⟩
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨q₁, h₁, hq₁⟩ := hlift x x.2
    obtain ⟨q₂, h₂, hq₂⟩ := hlift y y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hq₁, ← hq₂, ← map_mul, ← map_mul,
      hcomm q₁ h₁ q₂ h₂]
  · obtain ⟨q, hq, rfl⟩ := hlift x hx
    rw [← map_pow, hexp q hq, map_one]

private theorem isQuasisimple_alternatingGroup {n : ℕ} (hn : 5 ≤ n) :
    CFSG.Open.IsQuasisimple (alternatingGroup (Fin n)) := by
  have hcard : 5 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup hcard
  have hc : center (alternatingGroup (Fin n)) = ⊥ := alternatingGroup.center_eq_bot (by omega)
  let eq : alternatingGroup (Fin n) ⧸ center (alternatingGroup (Fin n)) ≃*
      alternatingGroup (Fin n) := (QuotientGroup.quotientMulEquivOfEq hc).trans
    QuotientGroup.quotientBot
  refine ⟨?_, eq.isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin n))) with
    h | h
  · exfalso
    have htop : center (alternatingGroup (Fin n)) = ⊤ := by
      refine eq_top_iff.2 fun a _ => mem_center_iff.2 fun b => ?_
      have hab : _ ∈ commutator (alternatingGroup (Fin n)) :=
        commutator_mem_commutator (mem_top b) (mem_top a)
      rw [h, mem_bot] at hab
      exact commutatorElement_eq_one_iff_mul_comm.1 hab
    exact bot_ne_top (hc.symm.trans htop)
  · exact h

theorem isComponentOf_of_mulEquiv {X : Subgroup K} {n : ℕ} (hn : 5 ≤ n)
    (hXsn : CFSG.Open.IsSubnormal X ⊤) (e : X ≃* alternatingGroup (Fin n)) :
    IsComponentOf X ⊤ := by
  exact ⟨le_top, hXsn, CFSG.Open.IsQuasisimple.of_mulEquiv e (isQuasisimple_alternatingGroup hn)⟩

theorem commute_of_map_conj_ne {X : Subgroup K} {n : ℕ} (hn : 5 ≤ n)
    (hXsn : CFSG.Open.IsSubnormal X ⊤) (e : X ≃* alternatingGroup (Fin n)) {g h : K}
    (hgh : X.map (MulAut.conj g).toMonoidHom ≠ X.map (MulAut.conj h).toMonoidHom) :
    ∀ x ∈ X.map (MulAut.conj g).toMonoidHom, ∀ y ∈ X.map (MulAut.conj h).toMonoidHom,
      x * y = y * x := by
  have hcomp : ∀ k : K, IsComponentOf (X.map (MulAut.conj k).toMonoidHom) ⊤ := by
    intro k
    have hsn := hXsn.map (MulAut.conj k).toMonoidHom
    rw [Subgroup.map_top_of_surjective _ (MulAut.conj k).surjective] at hsn
    exact isComponentOf_of_mulEquiv hn hsn
      ((X.equivMapOfInjective _ (MulAut.conj k).injective).symm.trans e)
  have h1 := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hcomp g) (hcomp h)
    hgh
  intro x hx y hy
  have hxy := commutator_mem_commutator hx hy
  rw [h1, mem_bot] at hxy
  exact commutatorElement_eq_one_iff_mul_comm.1 hxy

private theorem map_conj_mul (H : Subgroup K) (g h : K) :
    (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      H.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem map_conj_one (H : Subgroup K) : H.map (MulAut.conj (1 : K)).toMonoidHom = H := by
  ext x
  simp

private theorem map_conj_eq_iff (H : Subgroup K) (g : K) :
    H.map (MulAut.conj g).toMonoidHom = H ↔ g ∈ normalizer (H : Set K) := by
  constructor
  · intro h
    refine mem_normalizer_fintype fun x hx => ?_
    have := mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rw [h] at this
    exact this
  · intro hg
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hg y).1 hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (mem_normalizer_iff.1 hg _).2 ?_, ?_⟩
      · simpa [mul_assoc] using hx
      · simp [mul_assoc]

private theorem isElemAbelian_comap {f : K →* K} (hf : Function.Injective f) {p : ℕ}
    {P : Subgroup K} (hP : IsElemAbelian p P) : IsElemAbelian p (P.comap f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · have := hP.1.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩
    simpa [map_mul] using congrArg Subtype.val this
  · rw [map_pow, hP.2 _ hx, map_one]

theorem inf_map_conj_eq_bot {X : Subgroup K} {n : ℕ} (hn : 5 ≤ n)
    (hXsn : CFSG.Open.IsSubnormal X ⊤) (e : X ≃* alternatingGroup (Fin n)) {g : K}
    (hg : X.map (MulAut.conj g).toMonoidHom ≠ X) :
    X ⊓ X.map (MulAut.conj g).toMonoidHom = ⊥ := by
  have h1 : X.map (MulAut.conj (1 : K)).toMonoidHom = X := map_conj_one X
  have hcomm := commute_of_map_conj_ne hn hXsn e (g := 1) (h := g) (by rw [h1]; exact hg.symm)
  rw [eq_bot_iff]
  rintro z ⟨hzX, hzg⟩
  have hcen : e ⟨z, hzX⟩ ∈ center (alternatingGroup (Fin n)) := by
    rw [mem_center_iff]
    intro a
    obtain ⟨y, rfl⟩ := e.surjective a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm y (by rw [h1]; exact y.2) z hzg)
  rw [alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega),
    mem_bot, ← map_one e, e.injective.eq_iff] at hcen
  have h2 := congrArg (fun y : X => (y : K)) hcen
  exact h2

theorem exists_subgroup_of_not_le_normalizer {X T : Subgroup K} {n : ℕ} (hn : 8 ≤ n)
    (hXsn : CFSG.Open.IsSubnormal X ⊤) (e : X ≃* alternatingGroup (Fin n)) (hT : IsPGroup 2 T)
    (hTX : ¬ T ≤ normalizer (X : Set K)) :
    ∃ J : Subgroup K, T ≤ normalizer (J : Set K) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card J → p = 2 ∨ p = 3) ∧
      (∀ P : Subgroup K, P ≤ J → IsPGroup 3 P → IsElemAbelian 3 P) ∧ 27 ∣ Nat.card J := by
  classical
  obtain ⟨J₁, hJ₁X, hSJ₁, h23, hel, hJ₁9, -⟩ := exists_fibre_subgroup_of_mulEquiv
    (S := T ⊓ normalizer (X : Set K)) hn e (hT.to_le inf_le_left) inf_le_right
  obtain ⟨c, hcdef⟩ : ∃ c : K → Subgroup K, ∀ g, c g = J₁.map (MulAut.conj g).toMonoidHom :=
    ⟨_, fun _ => rfl⟩
  have hcard : ∀ a, Nat.card (c a) = Nat.card J₁ := fun a => by
    rw [hcdef]
    exact Subgroup.card_map_of_injective (MulAut.conj a).injective
  have hceq : ∀ a t : K, a ∈ T → t ∈ T →
      X.map (MulAut.conj a).toMonoidHom = X.map (MulAut.conj t).toMonoidHom → c a = c t := by
    intro a t ha ht hat
    have hs : t⁻¹ * a ∈ normalizer (X : Set K) := by
      rw [← map_conj_eq_iff, ← map_conj_mul, hat, map_conj_mul, inv_mul_cancel, map_conj_one]
    have hsJ : t⁻¹ * a ∈ normalizer (J₁ : Set K) := hSJ₁ ⟨T.mul_mem (T.inv_mem ht) ha, hs⟩
    calc c a = J₁.map (MulAut.conj a).toMonoidHom := hcdef a
      _ = (J₁.map (MulAut.conj (t⁻¹ * a)).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
          rw [map_conj_mul, mul_inv_cancel_left]
      _ = c t := by rw [(map_conj_eq_iff J₁ _).2 hsJ, hcdef]
  have hela : ∀ a : K, ∀ P : Subgroup K, P ≤ c a → IsPGroup 3 P → IsElemAbelian 3 P := by
    intro a P hP hP3
    rw [hcdef] at hP
    have hle : P.map (MulAut.conj a⁻¹).toMonoidHom ≤ J₁ := by
      have := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hP
      rwa [map_conj_mul, inv_mul_cancel, map_conj_one] at this
    have h := isElemAbelian_comap (f := (MulAut.conj a⁻¹).toMonoidHom)
      (MulAut.conj a⁻¹).injective (hel _ hle (hP3.map _))
    rwa [comap_map_eq_self_of_injective (f := (MulAut.conj a⁻¹).toMonoidHom)
      (MulAut.conj a⁻¹).injective] at h
  have hind : ∀ F : Finset K, (∀ t ∈ F, t ∈ T) →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card (F.sup c : Subgroup K) → p = 2 ∨ p = 3) ∧
      (∀ P : Subgroup K, P ≤ F.sup c → IsPGroup 3 P → IsElemAbelian 3 P) := by
    intro F
    refine Finset.induction_on F ?_ ?_
    · intro _
      rw [Finset.sup_empty]
      refine ⟨fun p hp hdvd => ?_, fun P hP _ => ?_⟩
      · rw [Subgroup.card_bot] at hdvd
        exact absurd (Nat.dvd_one.1 hdvd) hp.ne_one
      · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
        · rw [Subgroup.coe_mul, Subgroup.coe_mul, mem_bot.1 (hP a.2), mem_bot.1 (hP b.2)]
        · rw [mem_bot.1 (hP hx), one_pow]
    · intro a F haF ih hF
      obtain ⟨ih1, ih2⟩ := ih fun t ht => hF t (Finset.mem_insert_of_mem ht)
      have haT : a ∈ T := hF a (Finset.mem_insert_self a F)
      rw [Finset.sup_insert]
      by_cases hle : c a ≤ F.sup c
      · rw [sup_eq_right.2 hle]
        exact ⟨ih1, ih2⟩
      have hne : ∀ t ∈ F,
          X.map (MulAut.conj a).toMonoidHom ≠ X.map (MulAut.conj t).toMonoidHom := by
        intro t ht hXat
        apply hle
        rw [hceq a t haT (hF t (Finset.mem_insert_of_mem ht)) hXat]
        exact Finset.le_sup ht
      have hcen : F.sup c ≤ centralizer (c a : Set K) := by
        refine Finset.sup_le fun t ht => ?_
        intro y hy
        rw [mem_centralizer_iff]
        intro x hx
        rw [hcdef] at hx hy
        exact commute_of_map_conj_ne (by omega) hXsn e (hne t ht) x (map_mono hJ₁X hx) y
          (map_mono hJ₁X hy)
      have hcomm : ∀ x ∈ c a, ∀ y ∈ F.sup c, x * y = y * x := fun x hx y hy =>
        mem_centralizer_iff.1 (hcen hy) x hx
      refine ⟨fun p hp hdvd => ?_, isElemAbelian_of_le_sup_of_commute hcomm (hela a) ih2⟩
      rcases (Nat.Prime.dvd_mul hp).1 (hdvd.trans (card_sup_dvd_of_commute hcomm)) with h | h
      · rw [hcard a] at h
        exact h23 p hp h
      · exact ih1 p hp h
  set Fs : Finset K := (Set.toFinite (T : Set K)).toFinset with hFs
  have hmemFs : ∀ t, t ∈ Fs ↔ t ∈ T := fun t => Set.Finite.mem_toFinset _
  obtain ⟨hJ23, hJel⟩ := hind Fs fun t ht => (hmemFs t).1 ht
  refine ⟨Fs.sup c, ?_, hJ23, hJel, ?_⟩
  · intro s hs
    have hle : Fs.sup c ≤ (Fs.sup c).comap (MulAut.conj s).toMonoidHom := by
      refine Finset.sup_le fun t ht => ?_
      rw [← map_le_iff_le_comap, hcdef, map_conj_mul, ← hcdef]
      exact Finset.le_sup ((hmemFs _).2 (T.mul_mem hs ((hmemFs t).1 ht)))
    exact mem_normalizer_fintype fun h hh => hle hh
  · obtain ⟨t, htT, htN⟩ := SetLike.not_le_iff_exists.1 hTX
    have hXt : X.map (MulAut.conj t).toMonoidHom ≠ X := fun h =>
      htN ((map_conj_eq_iff X t).1 h)
    have hcomm := commute_of_map_conj_ne (by omega) hXsn e (g := 1) (h := t)
      (by rw [map_conj_one]; exact hXt.symm)
    have hJ₁t : ∀ x ∈ J₁, ∀ y ∈ c t, x * y = y * x := by
      intro x hx y hy
      rw [hcdef] at hy
      exact hcomm x (by rw [map_conj_one]; exact hJ₁X hx) y (map_mono hJ₁X hy)
    have hinf : J₁ ⊓ c t = ⊥ := by
      rw [eq_bot_iff, ← inf_map_conj_eq_bot (by omega) hXsn e hXt, hcdef]
      exact inf_le_inf hJ₁X (map_mono hJ₁X)
    have hsup : J₁ ⊔ c t ≤ Fs.sup c := by
      refine sup_le ?_ (Finset.le_sup ((hmemFs t).2 htT))
      have := Finset.le_sup (f := c) ((hmemFs 1).2 T.one_mem)
      rwa [hcdef, map_conj_one] at this
    have h81 : 81 ∣ Nat.card (J₁ ⊔ c t : Subgroup K) := by
      rw [card_sup_of_commute hJ₁t hinf, hcard]
      exact (by norm_num : (81 : ℕ) ∣ 9 * 9).trans (mul_dvd_mul hJ₁9 hJ₁9)
    exact (by norm_num : (27 : ℕ) ∣ 81).trans (h81.trans (Subgroup.card_dvd_of_le hsup))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen
