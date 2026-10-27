module

public import CFSG.Quasithin.Background.RonanE111Trans
public import CFSG.Quasithin.Background.RonanE111Gen
public import CFSG.Quasithin.Background.E1Sec8
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement


section Aux

variable {G G' : Type} [Group G] [Group G']

theorem normal_subgroupOf_map {N H : Subgroup G} (f : G →* G') (hNH : (N.subgroupOf H).Normal) (hle : N ≤ H) :
    ((N.map f).subgroupOf (H.map f)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hle)]
  have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hNH
  exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map f)

theorem mulEquiv_map_of_injOn {S : Subgroup G} (f : G →* G') (hinj : ∀ x ∈ S, f x = 1 → x = 1) :
    Nonempty (↥S ≃* ↥(S.map f)) := by
  have hi : Function.Injective (f.comp S.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hinj x x.2 hx)
  have hr : (f.comp S.subtype).range = S.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr)⟩

theorem isSimpleGroup_map_of_injOn {S : Subgroup G} (f : G →* G') (hinj : ∀ x ∈ S, f x = 1 → x = 1)
    (hS : IsSimpleGroup ↥S) : IsSimpleGroup ↥(S.map f) := by
  obtain ⟨e⟩ := mulEquiv_map_of_injOn f hinj
  exact (MulEquiv.isSimpleGroup_congr e).mp hS

theorem nonabelian_map_of_injOn {S : Subgroup G} (f : G →* G') (hinj : ∀ x ∈ S, f x = 1 → x = 1)
    (hS : ∃ a b : ↥S, a * b ≠ b * a) : ∃ a b : ↥(S.map f), a * b ≠ b * a := by
  obtain ⟨e⟩ := mulEquiv_map_of_injOn f hinj
  obtain ⟨a, b, hab⟩ := hS
  refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact h

theorem ne_bot_of_isSylowIn {P S : Subgroup G} (hP : IsSylowIn 2 P S) [Finite G]
    (hinv : ∃ x ∈ S, x ≠ 1 ∧ x ^ 2 = 1) : P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := hP.card_eq
  obtain ⟨x, hxS, hx1, hx2⟩ := hinv
  have ho : orderOf (⟨x, hxS⟩ : ↥S) = 2 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hx2)) (fun h => hx1 (congrArg Subtype.val h))
  have h2 : 2 ∣ Nat.card S := ho ▸ orderOf_dvd_natCard _
  have hv : 1 ≤ (Nat.card S).factorization 2 :=
    (Nat.prime_two.dvd_iff_one_le_factorization Nat.card_pos.ne').mp h2
  intro hbot
  rw [hbot, Subgroup.card_bot] at hc
  have : 2 ≤ 2 ^ (Nat.card S).factorization 2 :=
    le_self_pow₀ (by norm_num) (by omega)
  omega

end Aux

theorem isE_mono_of_one_le {G : Type} [Group G] {n : ℕ} (hn : 1 ≤ n) {H T A K : Subgroup G}
    (hK : E1.IsE 1 H T A K) : E1.IsE n H T A K := by
  obtain ⟨h1, h2, h3, h4 | h4⟩ := hK
  · exact ⟨h1, h2, h3, Or.inl ⟨h4.1, h4.2.trans (Nat.pow_le_pow_right (by norm_num) hn)⟩⟩
  · exact ⟨h1, h2, h3, Or.inr ⟨h4.1, h4.2.trans (Nat.pow_le_pow_right (by norm_num) hn)⟩⟩

section LS

variable {Q : Type} [Group Q]

theorem lift_semisimple [Finite Q] {n : ℕ} (hn : 1 ≤ n)
    {T T₀ D Y A : Subgroup Q} {𝒟 : Set (Subgroup Q)} [Y.Normal] [D.Normal]
    (hT : IsSylowIn 2 T ⊤) (hT₀T : T₀ ≤ T) (hAT₀ : A ≤ T₀) (hAab : IsElemAbelian 2 A)
    (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t)
    (hDperf : ⁅D, D⁆ = D) (hDT₀ : D ⊔ T₀ = ⊤) (hYs : Group.IsSolvable ↥Y)
    (hSM : SemisimpleMod T₀ D Y 𝒟) (hmove : ∃ S ∈ 𝒟, ¬ A ≤ Cmod S Y)
    (hrank : ∀ S ∈ 𝒟, ¬ A ⊓ Subgroup.normalizer (S : Set Q) ≤ Cmod S Y →
      (A ⊓ Subgroup.normalizer (S : Set Q) ⊓ Cmod S Y).relIndex
        (A ⊓ Subgroup.normalizer (S : Set Q)) ≤ 2 ^ n) :
    D ≤ T ⊔ ⨆ K ∈ {K : Subgroup Q | E1.IsE n ⊤ T A K}, K := by
  classical
  obtain ⟨S₀, hS₀, hAS₀⟩ := hmove
  have hYD : Y ≤ D := (hSM.Y_le S₀ hS₀).trans (hSM.le_D S₀ hS₀)
  have hT2 : IsPGroup 2 T := hT.2.1
  have hT₀2 : IsPGroup 2 T₀ := hT2.to_le hT₀T
  have hDT : D ⊔ T = ⊤ := by
    rw [eq_top_iff, ← hDT₀]
    exact sup_le_sup le_rfl hT₀T
  have hπ₁s : Function.Surjective (QuotientGroup.mk' Y) := QuotientGroup.mk'_surjective Y
  haveI hDn' : (D.map (QuotientGroup.mk' Y)).Normal := Subgroup.Normal.map ‹D.Normal› _ hπ₁s
  have hsf := hSM.semiFam_map
  have hDs := hSM.sSup_map
  have hTs : IsSylowIn 2 (T.map (QuotientGroup.mk' Y)) ⊤ := E1.isSylowIn_two_map_top hπ₁s hT
  have hQs : D.map (QuotientGroup.mk' Y) ⊔ T.map (QuotientGroup.mk' Y) = ⊤ := by
    rw [← Subgroup.map_sup, hDT, Subgroup.map_top_of_surjective _ hπ₁s]
  have hconj : ∀ Ŝ ∈ ((fun S : Subgroup Q => S.map (QuotientGroup.mk' Y)) '' 𝒟),
      ∀ t' ∈ T.map (QuotientGroup.mk' Y), A1b.conjSub t' Ŝ ∈
        ((fun S : Subgroup Q => S.map (QuotientGroup.mk' Y)) '' 𝒟) := by
    rintro _ ⟨S, hS, rfl⟩ _ ⟨t, ht, rfl⟩
    exact ⟨A1b.conjSub t S, hSM.conj_of_sup_top hDT₀ t hS, E1.map_conjSub _ t S⟩
  have htr : ∀ Ŝ ∈ ((fun S : Subgroup Q => S.map (QuotientGroup.mk' Y)) '' 𝒟),
      ∀ Ŝ' ∈ ((fun S : Subgroup Q => S.map (QuotientGroup.mk' Y)) '' 𝒟),
        ∃ t' ∈ T.map (QuotientGroup.mk' Y), A1b.conjSub t' Ŝ = Ŝ' := by
    rintro _ ⟨S, hS, rfl⟩ _ ⟨S', hS', rfl⟩
    obtain ⟨t, ht, hts⟩ := hSM.trans S hS S' hS'
    exact ⟨QuotientGroup.mk' Y t, ⟨t, hT₀T ht, rfl⟩, by rw [← E1.map_conjSub, hts]⟩
  have hR := reduced_quot_of_semiFam (Q' := Q ⧸ Y) (T := T.map (QuotientGroup.mk' Y))
    (D := D.map (QuotientGroup.mk' Y)) (C := centMod D Y) rfl hTs hsf hDs hQs
    ⟨_, ⟨S₀, hS₀, rfl⟩⟩ hconj htr
  have hZ : D.map (QuotientGroup.mk' Y) ⊓ centMod D Y = ⊥ := by
    show D.map (QuotientGroup.mk' Y) ⊓ Subgroup.centralizer
      ((D.map (QuotientGroup.mk' Y) : Subgroup (Q ⧸ Y)) : Set (Q ⧸ Y)) = ⊥
    rw [← hDs]
    exact inf_centralizer_eq_bot hsf
  have hπ₂inj : ∀ x ∈ D.map (QuotientGroup.mk' Y),
      QuotientGroup.mk' (centMod D Y) x = 1 → x = 1 := by
    intro x hx h1
    have h2 : x ∈ D.map (QuotientGroup.mk' Y) ⊓ centMod D Y := ⟨hx, (QuotientGroup.eq_one_iff x).mp h1⟩
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have hS₀D : S₀.map (QuotientGroup.mk' Y) ≤ D.map (QuotientGroup.mk' Y) :=
    Subgroup.map_mono (hSM.le_D S₀ hS₀)
  have hS₀n : ((S₀.map (QuotientGroup.mk' Y)).subgroupOf (D.map (QuotientGroup.mk' Y))).Normal := by
    have := hsf.normal ⟨S₀, hS₀, rfl⟩
    rwa [hDs] at this
  have hS₀simple : IsSimpleGroup ↥(S₀.map (QuotientGroup.mk' Y)) := hsf.simple _ ⟨S₀, hS₀, rfl⟩
  have hS₀nab : ∃ a b : ↥(S₀.map (QuotientGroup.mk' Y)), a * b ≠ b * a :=
    hsf.nonabelian _ ⟨S₀, hS₀, rfl⟩
  have hSb : IsComp ((D.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y)))
      ((S₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y))) := by
    have hinj : ∀ x ∈ S₀.map (QuotientGroup.mk' Y), QuotientGroup.mk' (centMod D Y) x = 1 → x = 1 :=
      fun x hx => hπ₂inj x (hS₀D hx)
    exact ⟨Subgroup.map_mono hS₀D, normal_subgroupOf_map _ hS₀n hS₀D,
      isSimpleGroup_map_of_injOn _ hinj hS₀simple, nonabelian_map_of_injOn _ hinj hS₀nab⟩
  have hAT : A ≤ T := hAT₀.trans hT₀T
  have hAsT : A.map (QuotientGroup.mk' Y) ≤ T.map (QuotientGroup.mk' Y) := Subgroup.map_mono hAT
  have hAsab : IsElemAbelian 2 (A.map (QuotientGroup.mk' Y)) := CFSG.Open.IsElemAbelian.map hAab _
  have hAbab : IsElemAbelian 2 ((A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y))) :=
    CFSG.Open.IsElemAbelian.map hAsab _
  have hAS : ¬ (A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y)) ≤
      Subgroup.centralizer ((((S₀.map (QuotientGroup.mk' Y)).map
        (QuotientGroup.mk' (centMod D Y))) : Subgroup _) : Set _) := by
    intro h
    apply hAS₀
    intro a ha
    exact (mem_centralizer_quot_iff hZ (hSM.Y_le S₀ hS₀) (hSM.le_D S₀ hS₀) a).mp
      (h ⟨_, ⟨a, ha, rfl⟩, rfl⟩)
  have hrank' : ¬ ((A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y))) ⊓
        Subgroup.normalizer ((((S₀.map (QuotientGroup.mk' Y)).map
          (QuotientGroup.mk' (centMod D Y))) : Subgroup _) : Set _) ≤
        Subgroup.centralizer ((((S₀.map (QuotientGroup.mk' Y)).map
          (QuotientGroup.mk' (centMod D Y))) : Subgroup _) : Set _) →
      Nat.card ↥(actOn ((S₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y)))
        ((A.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y)))) ≤ 2 ^ n := by
    intro hnot
    rw [card_actOn_quot hZ (hSM.Y_le S₀ hS₀) (hSM.le_D S₀ hS₀) A]
    apply hrank S₀ hS₀
    intro hle
    apply hnot
    rintro _ ⟨hx1, hx2⟩
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hx1
    have ha' : a ∈ Subgroup.normalizer (S₀ : Set Q) :=
      (mem_normalizer_quot_iff hZ (hSM.Y_le S₀ hS₀) (hSM.le_D S₀ hS₀) a).mp hx2
    exact (mem_centralizer_quot_iff hZ (hSM.Y_le S₀ hS₀) (hSM.le_D S₀ hS₀) a).mpr
      (hle ⟨ha, ha'⟩)
  obtain ⟨Kb, hKb, hcov⟩ := exists_member_comp hR hn (Subgroup.map_mono hAsT) hAbab hSb hAS hrank'
  obtain ⟨J₁, hJ₁, hJ₁K⟩ := E1.ten_seven (G := Q ⧸ Y) (T := T.map (QuotientGroup.mk' Y))
    (A := A.map (QuotientGroup.mk' Y)) (Y := centMod D Y) hTs hAsT hAsab hKb
  obtain ⟨J, hJ, hJJ₁⟩ := E1.ten_seven (G := Q) (T := T) (A := A) (Y := Y) hT hAT hAab hJ₁
  have hTb : IsSylowIn 2 ((T.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y))) ⊤ :=
    hR.2.2.2.2.2.1
  have hSbH : (S₀.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y)) ≤
      twoResidual Kb ⊔ (T.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y)) := by
    refine le_of_diag hSb.simple (inf_ne_bot hR hSb (exists_involution_of_isComp hSb)) le_sup_right ?_
    intro x hx
    obtain ⟨y, hy, hc⟩ := hcov x hx
    refine ⟨y, ?_, hc⟩
    exact (E1.le_twoResidual_sup_of_isSylowIn hKb.2.2.1).trans
      (sup_le_sup le_rfl inf_le_left) hy
  have hinvS₀ : ∃ x ∈ S₀.map (QuotientGroup.mk' Y), x ≠ 1 ∧ x ^ 2 = 1 :=
    exists_involution_of_isComp (X := D.map (QuotientGroup.mk' Y))
      (⟨hS₀D, hS₀n, hS₀simple, hS₀nab⟩ : IsComp (D.map (QuotientGroup.mk' Y))
        (S₀.map (QuotientGroup.mk' Y)))
  have hTS₀ : (T.map (QuotientGroup.mk' Y)) ⊓ S₀.map (QuotientGroup.mk' Y) ≠ ⊥ := by
    have hTD : IsSylowIn 2 ((T.map (QuotientGroup.mk' Y)) ⊓ D.map (QuotientGroup.mk' Y))
        (D.map (QuotientGroup.mk' Y)) := hTs.inf_normal le_top inferInstance
    have hTS : IsSylowIn 2 ((T.map (QuotientGroup.mk' Y)) ⊓ D.map (QuotientGroup.mk' Y) ⊓
        S₀.map (QuotientGroup.mk' Y)) (S₀.map (QuotientGroup.mk' Y)) := hTD.inf_normal hS₀D hS₀n
    have hne := ne_bot_of_isSylowIn hTS hinvS₀
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ (T.map (QuotientGroup.mk' Y)) ⊓ S₀.map (QuotientGroup.mk' Y) := ⟨hx.1.1, hx.2⟩
    rw [hbot] at this
    exact this
  have hS₀H₁ : S₀.map (QuotientGroup.mk' Y) ≤
      twoResidual J₁ ⊔ T.map (QuotientGroup.mk' Y) := by
    refine le_of_diag hS₀simple hTS₀ le_sup_right ?_
    intro x hx
    have hx' : QuotientGroup.mk' (centMod D Y) x ∈
        twoResidual Kb ⊔ (T.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y)) :=
      hSbH ⟨x, hx, rfl⟩
    have hHbeq : twoResidual Kb ⊔ (T.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y)) =
        (twoResidual J₁ ⊔ T.map (QuotientGroup.mk' Y)).map (QuotientGroup.mk' (centMod D Y)) := by
      rw [Subgroup.map_sup, hJ₁K]
    rw [hHbeq] at hx'
    obtain ⟨h, hh, hhx⟩ := hx'
    refine ⟨h, hh, ?_⟩
    have hker : x⁻¹ * h ∈ centMod D Y := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (centMod D Y) (x⁻¹ * h) = 1
      rw [map_mul, map_inv, hhx, inv_mul_cancel]
    exact Subgroup.centralizer_le (by exact_mod_cast hS₀D) hker
  have hDH₁ : D.map (QuotientGroup.mk' Y) ≤ twoResidual J₁ ⊔ T.map (QuotientGroup.mk' Y) := by
    rw [← hDs]
    refine sSup_le ?_
    rintro _ ⟨S, hS, rfl⟩
    obtain ⟨t, ht, hts⟩ := hSM.trans S₀ hS₀ S hS
    rw [← hts]
    beta_reduce
    rw [E1.map_conjSub]
    intro x hx
    rw [A1b.mem_conjSub_iff] at hx
    have hπt : QuotientGroup.mk' Y t ∈ twoResidual J₁ ⊔ T.map (QuotientGroup.mk' Y) :=
      Subgroup.mem_sup_right ⟨t, hT₀T ht, rfl⟩
    have h1 := hS₀H₁ hx
    have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ hπt h1) (Subgroup.inv_mem _ hπt)
    simpa [mul_assoc] using h2
  have hH₁eq : twoResidual J₁ ⊔ T.map (QuotientGroup.mk' Y) =
      (twoResidual J ⊔ T).map (QuotientGroup.mk' Y) := by
    rw [Subgroup.map_sup, hJJ₁]
  have hDH : D ≤ (twoResidual J ⊔ T) ⊔ Y := by
    intro d hd
    have h1 : QuotientGroup.mk' Y d ∈ (twoResidual J ⊔ T).map (QuotientGroup.mk' Y) :=
      hH₁eq ▸ hDH₁ ⟨d, hd, rfl⟩
    have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' Y) (twoResidual J ⊔ T)
    rw [QuotientGroup.ker_mk'] at h2
    have hmem : d ∈ ((twoResidual J ⊔ T).map (QuotientGroup.mk' Y)).comap (QuotientGroup.mk' Y) := h1
    rwa [h2] at hmem
  have hJ''Y : (twoResidual J ⊔ T) ⊔ Y = ⊤ := by
    rw [eq_top_iff, ← hDT₀]
    exact sup_le hDH ((hT₀T.trans le_sup_right).trans le_sup_left)
  obtain ⟨hres_D, hcore_D⟩ := twoResidual_top_of_perfect hDperf hT₀2 hDT₀
  have hres : twoResidual (⊤ : Subgroup Q) = perfectCore (⊤ : Subgroup Q) := by
    rw [hres_D, hcore_D]
  have hcomm : perfectCore (⊤ : Subgroup Q) = ⁅perfectCore (⊤ : Subgroup Q), A⁆ := by
    rw [hcore_D]
    exact eq_commutator_of_le_sup hDperf hYD hYs
      (D_le_commutator_sup hAab hAT₀ hT₀A hSM ⟨S₀, hS₀, hAS₀⟩)
  have h8 := E1.ten_eight_aux (Nat.card Q) Q le_rfl (T := T) (A := A) (Y := Y)
    (J := twoResidual J ⊔ T) hT hAT hAab hres hcomm hYs le_sup_right hJ''Y
  have hD8 : D ≤ (twoResidual J ⊔ T) ⊔ ⨆ K ∈ {K : Subgroup Q | E1.IsE 1 ⊤ T A K}, K := by
    rw [h8]
    exact le_top
  refine hD8.trans (sup_le (sup_le ?_ ?_) ?_)
  · exact le_sup_of_le_right ((twoResidual_le J).trans (le_iSup₂_of_le J hJ le_rfl))
  · exact le_sup_left
  · exact le_sup_of_le_right (iSup₂_le fun K hK =>
      le_iSup₂_of_le K (isE_mono_of_one_le hn hK) le_rfl)

end LS


end CFSG.Quasithin.RonanE111
