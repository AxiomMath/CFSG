module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridge
public import CFSG.LieType.Chevalley.WeylRoots
import CFSG.Mathlib.Decide.Nodup
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
open CFSG.EvenSmallLie.OmegaEight.Weyl CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[simp] theorem tmW8_rank_eq : Tag.E8.rank = 8 := by decide

@[expose] def tmW8_simpleIdx (i : Fin Tag.E8.rank) : ℕ :=
  if i.val = 0 then 175 else if i.val = 1 then 0 else if i.val = 2 then 2
  else if i.val = 3 then 30 else if i.val = 4 then 54 else if i.val = 5 then 74
  else if i.val = 6 then 90 else if i.val = 7 then 102 else 0

theorem tmW8_simpleIdx_lt (i : Fin Tag.E8.rank) : tmW8_simpleIdx i < 240 := by
  fin_cases i <;> decide

@[expose] def tmW8_a175 : Array ℕ :=
#[
  0, 177, 174, 3, 4, 178, 173, 7, 8, 180, 171, 11, 12, 184, 167, 15, 16, 192, 159, 19, 20, 208,
  143, 23, 112, 25, 26, 239, 172, 29, 30, 179, 170, 33, 34, 181, 166, 37, 38, 185, 158, 41, 42,
  193, 142, 45, 46, 209, 48, 238, 113, 51, 169, 53, 54, 182, 165, 57, 58, 186, 157, 61, 62, 194,
  141, 65, 66, 210, 68, 237, 114, 71, 163, 73, 74, 188, 155, 77, 78, 196, 139, 81, 82, 212, 84,
  235, 116, 87, 151, 89, 90, 200, 135, 93, 94, 216, 96, 231, 120, 99, 127, 101, 102, 224, 104,
  223, 128, 107, 108, 207, 144, 111, 24, 50, 70, 115, 86, 117, 118, 119, 98, 121, 122, 123, 124,
  125, 126, 100, 106, 129, 130, 131, 132, 133, 134, 92, 136, 137, 138, 80, 140, 64, 44, 22, 110,
  145, 146, 147, 148, 149, 150, 88, 152, 153, 154, 76, 156, 60, 40, 18, 160, 161, 162, 72, 164,
  56, 36, 14, 168, 52, 32, 10, 28, 6, 2, 176, 175, 1, 5, 31, 9, 35, 55, 183, 13, 39, 59, 187, 75,
  189, 190, 191, 17, 43, 63, 195, 79, 197, 198, 199, 91, 201, 202, 203, 204, 205, 206, 109, 21,
  47, 67, 211, 83, 213, 214, 215, 95, 217, 218, 219, 220, 221, 222, 105, 103, 225, 226, 227, 228,
  229, 230, 97, 232, 233, 234, 85, 236, 69, 49, 27,]

@[expose] def tmW8_a0 : Array ℕ :=
#[
  3, 1, 2, 0, 30, 31, 28, 29, 34, 35, 32, 33, 38, 39, 36, 37, 42, 43, 40, 41, 46, 47, 44, 45, 50,
  51, 48, 49, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27,
  24, 25, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
  74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
  98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 113, 112, 114, 115, 116,
  117, 119, 118, 120, 121, 123, 122, 125, 124, 126, 127, 128, 129, 131, 130, 133, 132, 134, 135,
  137, 136, 138, 139, 140, 141, 143, 142, 144, 145, 147, 146, 149, 148, 150, 151, 153, 152, 154,
  155, 156, 157, 159, 158, 161, 160, 162, 163, 164, 165, 167, 166, 168, 169, 171, 170, 173, 172,
  174, 175, 176, 177, 179, 178, 181, 180, 182, 183, 185, 184, 186, 187, 188, 189, 191, 190, 193,
  192, 194, 195, 196, 197, 199, 198, 200, 201, 203, 202, 205, 204, 206, 207, 209, 208, 210, 211,
  212, 213, 215, 214, 216, 217, 219, 218, 221, 220, 222, 223, 224, 225, 227, 226, 229, 228, 230,
  231, 233, 232, 234, 235, 236, 237, 239, 238,]

@[expose] def tmW8_a2 : Array ℕ :=
#[
  0, 2, 1, 3, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
  49, 50, 51, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
  74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
  98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 115, 114, 117,
  116, 118, 119, 121, 120, 122, 123, 124, 125, 127, 126, 129, 128, 130, 131, 132, 133, 135, 134,
  136, 137, 139, 138, 141, 140, 142, 143, 145, 144, 146, 147, 148, 149, 151, 150, 152, 153, 155,
  154, 157, 156, 158, 159, 160, 161, 163, 162, 165, 164, 166, 167, 169, 168, 170, 171, 172, 173,
  175, 174, 177, 176, 178, 179, 180, 181, 183, 182, 184, 185, 187, 186, 189, 188, 190, 191, 192,
  193, 195, 194, 197, 196, 198, 199, 201, 200, 202, 203, 204, 205, 207, 206, 208, 209, 211, 210,
  213, 212, 214, 215, 217, 216, 218, 219, 220, 221, 223, 222, 225, 224, 226, 227, 228, 229, 231,
  230, 232, 233, 235, 234, 237, 236, 238, 239,]

@[expose] def tmW8_a30 : Array ℕ :=
#[
  4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 30, 29, 31, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
  70, 71, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 72, 73,
  74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
  98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 114, 113, 115, 116,
  118, 117, 119, 120, 122, 121, 123, 124, 126, 125, 127, 128, 130, 129, 131, 132, 134, 133, 135,
  136, 138, 137, 139, 140, 142, 141, 143, 144, 146, 145, 147, 148, 150, 149, 151, 152, 154, 153,
  155, 156, 158, 157, 159, 160, 162, 161, 163, 164, 166, 165, 167, 168, 170, 169, 171, 172, 174,
  173, 175, 176, 178, 177, 179, 180, 182, 181, 183, 184, 186, 185, 187, 188, 190, 189, 191, 192,
  194, 193, 195, 196, 198, 197, 199, 200, 202, 201, 203, 204, 206, 205, 207, 208, 210, 209, 211,
  212, 214, 213, 215, 216, 218, 217, 219, 220, 222, 221, 223, 224, 226, 225, 227, 228, 230, 229,
  231, 232, 234, 233, 235, 236, 238, 237, 239,]

@[expose] def tmW8_a54 : Array ℕ :=
#[
  0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 32, 33, 34, 35, 28, 29, 30, 31, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
  50, 51, 52, 54, 53, 55, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 56, 57,
  58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
  98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 116, 117, 114,
  115, 118, 119, 120, 121, 124, 125, 122, 123, 126, 127, 128, 129, 132, 133, 130, 131, 134, 135,
  136, 137, 140, 141, 138, 139, 142, 143, 144, 145, 148, 149, 146, 147, 150, 151, 152, 153, 156,
  157, 154, 155, 158, 159, 160, 161, 164, 165, 162, 163, 166, 167, 168, 169, 172, 173, 170, 171,
  174, 175, 176, 177, 180, 181, 178, 179, 182, 183, 184, 185, 188, 189, 186, 187, 190, 191, 192,
  193, 196, 197, 194, 195, 198, 199, 200, 201, 204, 205, 202, 203, 206, 207, 208, 209, 212, 213,
  210, 211, 214, 215, 216, 217, 220, 221, 218, 219, 222, 223, 224, 225, 228, 229, 226, 227, 230,
  231, 232, 233, 236, 237, 234, 235, 238, 239,]

@[expose] def tmW8_a74 : Array ℕ :=
#[
  0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 36, 37, 38, 39, 32, 33, 34, 35, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
  50, 51, 56, 57, 58, 59, 52, 53, 54, 55, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 74,
  73, 75, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
  86, 87, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 120,
  121, 122, 123, 116, 117, 118, 119, 124, 125, 126, 127, 128, 129, 130, 131, 136, 137, 138, 139,
  132, 133, 134, 135, 140, 141, 142, 143, 144, 145, 146, 147, 152, 153, 154, 155, 148, 149, 150,
  151, 156, 157, 158, 159, 160, 161, 162, 163, 168, 169, 170, 171, 164, 165, 166, 167, 172, 173,
  174, 175, 176, 177, 178, 179, 184, 185, 186, 187, 180, 181, 182, 183, 188, 189, 190, 191, 192,
  193, 194, 195, 200, 201, 202, 203, 196, 197, 198, 199, 204, 205, 206, 207, 208, 209, 210, 211,
  216, 217, 218, 219, 212, 213, 214, 215, 220, 221, 222, 223, 224, 225, 226, 227, 232, 233, 234,
  235, 228, 229, 230, 231, 236, 237, 238, 239,]

@[expose] def tmW8_a90 : Array ℕ :=
#[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 17, 18, 19, 12, 13, 14, 15, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 40, 41, 42, 43, 36, 37, 38, 39, 44, 45, 46, 47, 48, 49,
  50, 51, 52, 53, 54, 55, 60, 61, 62, 63, 56, 57, 58, 59, 64, 65, 66, 67, 68, 69, 70, 71, 76, 77,
  78, 79, 72, 73, 74, 75, 80, 81, 82, 83, 84, 85, 86, 87, 88, 90, 89, 91, 100, 101, 102, 103,
  104, 105, 106, 107, 92, 93, 94, 95, 96, 97, 98, 99, 108, 109, 110, 111, 112, 113, 114, 115,
  116, 117, 118, 119, 128, 129, 130, 131, 132, 133, 134, 135, 120, 121, 122, 123, 124, 125, 126,
  127, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 160, 161,
  162, 163, 164, 165, 166, 167, 152, 153, 154, 155, 156, 157, 158, 159, 168, 169, 170, 171, 172,
  173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 192, 193, 194, 195, 196, 197, 198, 199,
  184, 185, 186, 187, 188, 189, 190, 191, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210,
  211, 212, 213, 214, 215, 224, 225, 226, 227, 228, 229, 230, 231, 216, 217, 218, 219, 220, 221,
  222, 223, 232, 233, 234, 235, 236, 237, 238, 239,]

@[expose] def tmW8_a102 : Array ℕ :=
#[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 20, 21, 22, 23, 16, 17, 18, 19, 24, 25,
  26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 44, 45, 46, 47, 40, 41, 42, 43, 48, 49,
  50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 64, 65, 66, 67, 60, 61, 62, 63, 68, 69, 70, 71, 72, 73,
  74, 75, 80, 81, 82, 83, 76, 77, 78, 79, 84, 85, 86, 87, 92, 93, 94, 95, 88, 89, 90, 91, 96, 97,
  98, 99, 100, 102, 101, 103, 108, 109, 110, 111, 104, 105, 106, 107, 112, 113, 114, 115, 116,
  117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 144, 145, 146, 147, 148, 149, 150, 151,
  152, 153, 154, 155, 156, 157, 158, 159, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138,
  139, 140, 141, 142, 143, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
  174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 208,
  209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 192, 193, 194, 195,
  196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 224, 225, 226, 227, 228, 229, 230,
  231, 232, 233, 234, 235, 236, 237, 238, 239,]

@[expose] def tmW8_a52 : Array ℕ :=
#[
  0, 1, 2, 3, 9, 8, 11, 10, 5, 4, 7, 6, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
  26, 27, 33, 32, 35, 34, 29, 28, 31, 30, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
  50, 51, 55, 53, 54, 52, 74, 75, 72, 73, 78, 79, 76, 77, 82, 83, 80, 81, 86, 87, 84, 85, 58, 59,
  56, 57, 62, 63, 60, 61, 66, 67, 64, 65, 70, 71, 68, 69, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97,
  98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 118, 119, 114, 115, 116,
  117, 112, 113, 126, 127, 122, 123, 124, 125, 120, 121, 134, 135, 130, 131, 132, 133, 128, 129,
  142, 143, 138, 139, 140, 141, 136, 137, 150, 151, 146, 147, 148, 149, 144, 145, 158, 159, 154,
  155, 156, 157, 152, 153, 166, 167, 162, 163, 164, 165, 160, 161, 174, 175, 170, 171, 172, 173,
  168, 169, 182, 183, 178, 179, 180, 181, 176, 177, 190, 191, 186, 187, 188, 189, 184, 185, 198,
  199, 194, 195, 196, 197, 192, 193, 206, 207, 202, 203, 204, 205, 200, 201, 214, 215, 210, 211,
  212, 213, 208, 209, 222, 223, 218, 219, 220, 221, 216, 217, 230, 231, 226, 227, 228, 229, 224,
  225, 238, 239, 234, 235, 236, 237, 232, 233,]

@[expose] def tmW8_a173 : Array ℕ :=
#[
  172, 1, 2, 179, 4, 175, 176, 7, 169, 9, 10, 182, 165, 13, 14, 186, 157, 17, 18, 194, 141, 21,
  22, 210, 24, 237, 114, 27, 28, 174, 177, 31, 168, 33, 34, 183, 164, 37, 38, 187, 156, 41, 42,
  195, 140, 45, 46, 211, 48, 236, 115, 51, 52, 180, 171, 55, 56, 184, 167, 59, 60, 192, 159, 63,
  64, 208, 143, 67, 112, 69, 70, 239, 161, 73, 74, 190, 153, 77, 78, 198, 137, 81, 82, 214, 84,
  233, 118, 87, 149, 89, 90, 202, 133, 93, 94, 218, 96, 229, 122, 99, 125, 101, 102, 226, 104,
  221, 130, 107, 108, 205, 146, 111, 68, 113, 26, 50, 116, 117, 86, 119, 120, 121, 98, 123, 124,
  100, 126, 127, 128, 129, 106, 131, 132, 92, 134, 135, 136, 80, 138, 139, 44, 20, 142, 66, 144,
  145, 110, 147, 148, 88, 150, 151, 152, 76, 154, 155, 40, 16, 158, 62, 160, 72, 162, 163, 36,
  12, 166, 58, 32, 8, 170, 54, 0, 178, 29, 5, 6, 30, 173, 3, 53, 181, 11, 35, 57, 185, 15, 39,
  188, 189, 75, 191, 61, 193, 19, 43, 196, 197, 79, 199, 200, 201, 91, 203, 204, 109, 206, 207,
  65, 209, 23, 47, 212, 213, 83, 215, 216, 217, 95, 219, 220, 105, 222, 223, 224, 225, 103, 227,
  228, 97, 230, 231, 232, 85, 234, 235, 49, 25, 238, 71,]

@[expose] def tmW8_a88 : Array ℕ :=
#[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 17, 16, 19, 18, 13, 12, 15, 14, 20, 21, 22, 23, 24, 25,
  26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 41, 40, 43, 42, 37, 36, 39, 38, 44, 45, 46, 47, 48, 49,
  50, 51, 52, 53, 54, 55, 61, 60, 63, 62, 57, 56, 59, 58, 64, 65, 66, 67, 68, 69, 70, 71, 77, 76,
  79, 78, 73, 72, 75, 74, 80, 81, 82, 83, 84, 85, 86, 87, 91, 89, 90, 88, 102, 103, 100, 101,
  106, 107, 104, 105, 94, 95, 92, 93, 98, 99, 96, 97, 108, 109, 110, 111, 136, 137, 138, 139,
  140, 141, 142, 143, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134,
  135, 112, 113, 114, 115, 116, 117, 118, 119, 168, 169, 170, 171, 172, 173, 174, 175, 152, 153,
  154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 144, 145, 146, 147, 148,
  149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 184, 185, 186, 187, 188, 189, 190, 191,
  192, 193, 194, 195, 196, 197, 198, 199, 176, 177, 178, 179, 180, 181, 182, 183, 232, 233, 234,
  235, 236, 237, 238, 239, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
  230, 231, 208, 209, 210, 211, 212, 213, 214, 215,]

@[expose] def tmW8_a110 : Array ℕ :=
#[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 24, 25, 26, 27, 20, 21,
  22, 23, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 48, 49, 50, 51, 44, 45,
  46, 47, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 68, 69, 70, 71, 64, 65, 66, 67, 72, 73,
  74, 75, 76, 77, 78, 79, 84, 85, 86, 87, 80, 81, 82, 83, 88, 89, 90, 91, 96, 97, 98, 99, 92, 93,
  94, 95, 104, 105, 106, 107, 100, 101, 102, 103, 108, 110, 109, 111, 112, 113, 114, 115, 116,
  117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135,
  136, 137, 138, 139, 140, 141, 142, 143, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186,
  187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205,
  206, 207, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160,
  161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 208, 209, 210, 211,
  212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230,
  231, 232, 233, 234, 235, 236, 237, 238, 239,]

@[expose] def tmW8_a108 : Array ℕ :=
#[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 25, 24, 27, 26, 21, 20,
  23, 22, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 49, 48, 51, 50, 45, 44,
  47, 46, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 69, 68, 71, 70, 65, 64, 67, 66, 72, 73,
  74, 75, 76, 77, 78, 79, 85, 84, 87, 86, 81, 80, 83, 82, 88, 89, 90, 91, 97, 96, 99, 98, 93, 92,
  95, 94, 105, 104, 107, 106, 101, 100, 103, 102, 111, 109, 110, 108, 208, 209, 210, 211, 212,
  213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231,
  232, 233, 234, 235, 236, 237, 238, 239, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154,
  155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173,
  174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192,
  193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 112, 113, 114, 115,
  116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134,
  135, 136, 137, 138, 139, 140, 141, 142, 143,]

private theorem tmW8_reflArr_eq_of_vectors (r : ℕ) (t : Array ℕ)
    (hsize : t.size = 240)
    (h : ∀ i : Fin 240, t[i.val]! < 240 ∧
      reflVec (rootVec r) (rootVec i.val) = rootVec t[i.val]!) :
    reflArr r = t := by
  have hnodup : rootList.Nodup :=
    CFSG.Decide.nodup_of_bitsetNodup
      (fun v => v.foldl (fun n x => 5 * n + (x + 2).toNat) 0) (by decide +kernel)
  have hlen : rootList.length = 240 := by decide +kernel
  apply Array.ext
  · simpa [reflArr] using hsize.symm
  · intro i hi ht
    have hi' : i < 240 := by simpa [reflArr] using hi
    obtain ⟨hj, hv⟩ := h ⟨i, hi'⟩
    have hj' : t[i]! < rootList.length := by simpa [hlen] using hj
    simp only [reflArr, Array.getElem_ofFn]
    rw [hv]
    unfold rootIdx CFSG.EvenSmallLie.OmegaEight.Weyl.rootVec
    rw [List.getD_eq_getElem _ _ hj', hnodup.idxOf_getElem]
    exact getElem!_pos t i ht

theorem tmW8_reflArr_175 : reflArr 175 = tmW8_a175 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_0 : reflArr 0 = tmW8_a0 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_2 : reflArr 2 = tmW8_a2 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_30 : reflArr 30 = tmW8_a30 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_54 : reflArr 54 = tmW8_a54 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_74 : reflArr 74 = tmW8_a74 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_90 : reflArr 90 = tmW8_a90 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_102 : reflArr 102 = tmW8_a102 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_52 : reflArr 52 = tmW8_a52 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_173 : reflArr 173 = tmW8_a173 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_88 : reflArr 88 = tmW8_a88 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_110 : reflArr 110 = tmW8_a110 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_reflArr_108 : reflArr 108 = tmW8_a108 := by
  apply tmW8_reflArr_eq_of_vectors _ _ (by decide +kernel)
  simp only [← Array.getElem!_toList]
  decide +kernel

@[expose] def tmW8_simpleValues : List ℕ := [175, 0, 2, 30, 54, 74, 90, 102]

@[expose] def tmW8_arr (r : ℕ) : Array ℕ :=
  if r = 175 then tmW8_a175 else if r = 0 then tmW8_a0 else if r = 2 then tmW8_a2
  else if r = 30 then tmW8_a30 else if r = 54 then tmW8_a54 else if r = 74 then tmW8_a74
  else if r = 90 then tmW8_a90 else if r = 102 then tmW8_a102 else if r = 52 then tmW8_a52
  else if r = 173 then tmW8_a173 else if r = 88 then tmW8_a88 else if r = 110 then tmW8_a110
  else if r = 108 then tmW8_a108 else #[]

theorem tmW8_arr_simple_eq (r : ℕ) (hr : r ∈ tmW8_simpleValues) :
    tmW8_arr r = reflArr r := by
  simp only [tmW8_simpleValues, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [tmW8_arr, tmW8_reflArr_175, tmW8_reflArr_0, tmW8_reflArr_2, tmW8_reflArr_30,
      tmW8_reflArr_54, tmW8_reflArr_74, tmW8_reflArr_90, tmW8_reflArr_102]

@[expose] def tmW8_adj (i j : ℕ) : Bool :=
  (i = 0 && j = 2) || (i = 2 && j = 0) || (i = 1 && j = 3) || (i = 3 && j = 1) ||
  (i = 2 && j = 3) || (i = 3 && j = 2) || (i = 3 && j = 4) || (i = 4 && j = 3) ||
  (i = 4 && j = 5) || (i = 5 && j = 4) || (i = 5 && j = 6) || (i = 6 && j = 5) ||
  (i = 6 && j = 7) || (i = 7 && j = 6)

@[expose] def tmW8_cartan (i j : ℕ) : ℤ :=
  if i = j then 2 else if tmW8_adj i j then -1 else 0

theorem tmW8_cartan_eq (i j : Fin Tag.E8.rank) :
    Tag.cartanE 8 i j = tmW8_cartan i.val j.val := by
  fin_cases i <;> fin_cases j <;> decide

@[expose] def tmW8_coxM (i j : Fin Tag.E8.rank) : ℕ :=
  if i.val = j.val then 1 else if tmW8_adj i.val j.val then 3 else 2

theorem tmW8_coxM_eq (i j : Fin Tag.E8.rank) :
    (coxeterMatrix (isFiniteType_cartan Tag.E8)) i j = tmW8_coxM i j := by
  rw [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  change TauCeti.coxeterOrder (Tag.cartanE 8 i j * Tag.cartanE 8 j i) = tmW8_coxM i j
  rw [tmW8_cartan_eq i j, tmW8_cartan_eq j i]
  fin_cases i <;> fin_cases j <;>
    simp [tmW8_cartan, tmW8_adj, tmW8_coxM, TauCeti.coxeterOrder_zero, TauCeti.coxeterOrder_one,
      TauCeti.coxeterOrder_four]

@[expose] def tmW8_eqA (t u : Array ℕ) : Bool := t.toList == u.toList

theorem tmW8_eqA_sound {n : ℕ} {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hu : Rep n u h) (hc : tmW8_eqA t u = true) : g = h := by
  have htu : t = u := by
    apply Array.toList_inj.1
    simpa [tmW8_eqA] using hc
  refine ht.unique ?_
  rw [htu]
  exact hu

@[expose] def tmW8_castIdx (i : Fin 8) : Fin Tag.E8.rank :=
  ⟨i.val, by rw [tmW8_rank_eq]; exact i.isLt⟩

@[expose] def tmW8_apply (l : List ℕ) (x : ℕ) : ℕ :=
  l.foldr (fun r y => (tmW8_arr r)[y]!) x

@[expose] def tmW8_wordArr (l : List ℕ) : Array ℕ :=
  Array.ofFn (n := 240) fun i => tmW8_apply l i.val

theorem tmW8_wordArr_cons (r : ℕ) (l : List ℕ) :
    tmW8_wordArr (r :: l) = compA 240 (tmW8_arr r) (tmW8_wordArr l) := by
  simp only [tmW8_wordArr, compA]
  refine congrArg (Array.ofFn (n := 240)) (funext fun i => ?_)
  rw [getElem!_pos (Array.ofFn fun k : Fin 240 => tmW8_apply l k.val) i.val (by simp),
    Array.getElem_ofFn]
  rfl

theorem tmW8_wordArr_eq (l : List ℕ) (h : ∀ r ∈ l, tmW8_arr r = reflArr r) :
    tmW8_wordArr l = wordArr l := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rw [tmW8_wordArr_cons, ih fun s hs => h s (List.mem_cons_of_mem _ hs), h r (by simp),
      wordArr]

theorem tmW8_mem_simple_of (l : List ℕ)
    (h : l.all (fun s => decide (s ∈ tmW8_simpleValues)) = true) :
    ∀ s ∈ l, s ∈ tmW8_simpleValues :=
  fun s hs => of_decide_eq_true ((List.all_eq_true.mp h) s hs)

theorem tmW8_allLt_of (l : List ℕ) (h : l.all (fun s => decide (s < 240)) = true) :
    ∀ s ∈ l, s < 240 :=
  fun s hs => of_decide_eq_true ((List.all_eq_true.mp h) s hs)

@[expose] def tmW8_nodes52 : List (Fin 8) :=
  [
  3, 4, 2, 3, 1, 3, 2, 4, 3,]

@[expose] def tmW8_root52 : List ℕ :=
  [
  30, 54, 2, 30, 0, 30, 2, 54, 30,]

@[expose] def tmW8_nodes173 : List (Fin 8) :=
  [
  3, 2, 0, 2, 3,]

@[expose] def tmW8_root173 : List ℕ :=
  [
  30, 2, 175, 2, 30,]

@[expose] def tmW8_nodes88 : List (Fin 8) :=
  [
  5, 6, 4, 5, 3, 4, 2, 3, 1, 3, 2, 4, 3, 5, 4, 6, 5,]

@[expose] def tmW8_root88 : List ℕ :=
  [
  74, 90, 54, 74, 30, 54, 2, 30, 0, 30, 2, 54, 30, 74, 54, 90, 74,]

@[expose] def tmW8_nodes110 : List (Fin 8) :=
  [
  0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2,
  0,]

@[expose] def tmW8_root110 : List ℕ :=
  [
  175, 2, 30, 54, 74, 90, 0, 30, 54, 74, 2, 30, 54, 0, 30, 2, 175, 2, 30, 0, 54, 30, 2, 74, 54,
  30, 0, 90, 74, 54, 30, 2, 175,]

@[expose] def tmW8_nodes108 : List (Fin 8) :=
  [
  7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 6, 1, 3, 4, 5, 2, 3, 4, 1, 3, 2, 0, 2, 3, 1,
  4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0, 7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7,]

@[expose] def tmW8_root108 : List ℕ :=
  [
  102, 90, 74, 54, 30, 2, 0, 30, 54, 74, 90, 102, 175, 2, 30, 54, 74, 90, 0, 30, 54, 74, 2, 30,
  54, 0, 30, 2, 175, 2, 30, 0, 54, 30, 2, 74, 54, 30, 0, 90, 74, 54, 30, 2, 175, 102, 90, 74, 54,
  30, 0, 2, 30, 54, 74, 90, 102,]

theorem tmW8_wordCheck52 : tmW8_eqA (tmW8_wordArr tmW8_root52) tmW8_a52 = true := by
  unfold tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_root52_simple : ∀ s ∈ tmW8_root52, s ∈ tmW8_simpleValues :=
  tmW8_mem_simple_of _ (by decide)

theorem tmW8_root52_lt : ∀ s ∈ tmW8_root52, s < 240 :=
  tmW8_allLt_of _ (by decide)

theorem tmW8_arr_mem_root52 : ∀ s ∈ tmW8_root52, tmW8_arr s = reflArr s :=
  fun s hs => tmW8_arr_simple_eq s (tmW8_root52_simple s hs)

theorem tmW8_root52_eq : (tmW8_nodes52.map tmW8_castIdx).map tmW8_simpleIdx = tmW8_root52 := by
  decide +kernel

theorem tmW8_wordCheck173 : tmW8_eqA (tmW8_wordArr tmW8_root173) tmW8_a173 = true := by
  unfold tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_root173_simple : ∀ s ∈ tmW8_root173, s ∈ tmW8_simpleValues :=
  tmW8_mem_simple_of _ (by decide)

theorem tmW8_root173_lt : ∀ s ∈ tmW8_root173, s < 240 :=
  tmW8_allLt_of _ (by decide)

theorem tmW8_arr_mem_root173 : ∀ s ∈ tmW8_root173, tmW8_arr s = reflArr s :=
  fun s hs => tmW8_arr_simple_eq s (tmW8_root173_simple s hs)

theorem tmW8_root173_eq : (tmW8_nodes173.map tmW8_castIdx).map tmW8_simpleIdx = tmW8_root173 := by
  decide +kernel

theorem tmW8_wordCheck88 : tmW8_eqA (tmW8_wordArr tmW8_root88) tmW8_a88 = true := by
  unfold tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_root88_simple : ∀ s ∈ tmW8_root88, s ∈ tmW8_simpleValues :=
  tmW8_mem_simple_of _ (by decide)

theorem tmW8_root88_lt : ∀ s ∈ tmW8_root88, s < 240 :=
  tmW8_allLt_of _ (by decide)

theorem tmW8_arr_mem_root88 : ∀ s ∈ tmW8_root88, tmW8_arr s = reflArr s :=
  fun s hs => tmW8_arr_simple_eq s (tmW8_root88_simple s hs)

theorem tmW8_root88_eq : (tmW8_nodes88.map tmW8_castIdx).map tmW8_simpleIdx = tmW8_root88 := by
  decide +kernel

theorem tmW8_wordCheck110 : tmW8_eqA (tmW8_wordArr tmW8_root110) tmW8_a110 = true := by
  unfold tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_root110_simple : ∀ s ∈ tmW8_root110, s ∈ tmW8_simpleValues :=
  tmW8_mem_simple_of _ (by decide)

theorem tmW8_root110_lt : ∀ s ∈ tmW8_root110, s < 240 :=
  tmW8_allLt_of _ (by decide)

theorem tmW8_arr_mem_root110 : ∀ s ∈ tmW8_root110, tmW8_arr s = reflArr s :=
  fun s hs => tmW8_arr_simple_eq s (tmW8_root110_simple s hs)

theorem tmW8_root110_eq : (tmW8_nodes110.map tmW8_castIdx).map tmW8_simpleIdx = tmW8_root110 := by
  decide +kernel

theorem tmW8_wordCheck108 : tmW8_eqA (tmW8_wordArr tmW8_root108) tmW8_a108 = true := by
  unfold tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_root108_simple : ∀ s ∈ tmW8_root108, s ∈ tmW8_simpleValues :=
  tmW8_mem_simple_of _ (by decide)

theorem tmW8_root108_lt : ∀ s ∈ tmW8_root108, s < 240 :=
  tmW8_allLt_of _ (by decide)

theorem tmW8_arr_mem_root108 : ∀ s ∈ tmW8_root108, tmW8_arr s = reflArr s :=
  fun s hs => tmW8_arr_simple_eq s (tmW8_root108_simple s hs)

theorem tmW8_root108_eq : (tmW8_nodes108.map tmW8_castIdx).map tmW8_simpleIdx = tmW8_root108 := by
  decide +kernel

theorem tmW8_simpleIdx_mem (i : Fin Tag.E8.rank) : tmW8_simpleIdx i ∈ tmW8_simpleValues := by
  fin_cases i <;> decide

@[expose] def tmW8_coxWord (i j : Fin Tag.E8.rank) : List ℕ :=
  (List.replicate (tmW8_coxM i j) [tmW8_simpleIdx i, tmW8_simpleIdx j]).flatten

theorem tmW8_mem_coxWord {i j : Fin Tag.E8.rank} {r : ℕ} (hr : r ∈ tmW8_coxWord i j) :
    r = tmW8_simpleIdx i ∨ r = tmW8_simpleIdx j := by
  simp only [tmW8_coxWord, List.mem_flatten, List.mem_replicate] at hr
  obtain ⟨l, ⟨-, rfl⟩, hr⟩ := hr
  simpa using hr

theorem tmW8_wordPerm_coxWord (i j : Fin Tag.E8.rank) :
    wordPerm (tmW8_coxWord i j) =
      (refl (tmW8_simpleIdx i) * refl (tmW8_simpleIdx j)) ^ tmW8_coxM i j := by
  rw [wordPerm, tmW8_coxWord]
  generalize tmW8_coxM i j = m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, List.map_append, List.prod_append, ih, pow_succ']
    simp

@[expose] def tmW8_coxRow (i : Fin Tag.E8.rank) : Bool :=
  (List.finRange Tag.E8.rank).all fun j =>
    tmW8_eqA (tmW8_wordArr (tmW8_coxWord i j)) (idA 240)

theorem tmW8_coxRow_0 : tmW8_coxRow ⟨0, by simp⟩ = true := by
  unfold tmW8_coxRow tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_coxRow_1 : tmW8_coxRow ⟨1, by simp⟩ = true := by
  unfold tmW8_coxRow tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_coxRow_2 : tmW8_coxRow ⟨2, by simp⟩ = true := by
  unfold tmW8_coxRow tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_coxRow_3 : tmW8_coxRow ⟨3, by simp⟩ = true := by
  unfold tmW8_coxRow tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_coxRow_4 : tmW8_coxRow ⟨4, by simp⟩ = true := by
  unfold tmW8_coxRow tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_coxRow_5 : tmW8_coxRow ⟨5, by simp⟩ = true := by
  unfold tmW8_coxRow tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_coxRow_6 : tmW8_coxRow ⟨6, by simp⟩ = true := by
  unfold tmW8_coxRow tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_coxRow_7 : tmW8_coxRow ⟨7, by simp⟩ = true := by
  unfold tmW8_coxRow tmW8_eqA tmW8_wordArr tmW8_apply
  simp only [← Array.getElem!_toList]
  decide +kernel

theorem tmW8_coxRow_eq (i : Fin Tag.E8.rank) : tmW8_coxRow i = true := by
  fin_cases i
  exacts [tmW8_coxRow_0, tmW8_coxRow_1, tmW8_coxRow_2, tmW8_coxRow_3, tmW8_coxRow_4,
    tmW8_coxRow_5, tmW8_coxRow_6, tmW8_coxRow_7]

theorem tmW8_coxRel
    (i j : Fin Tag.E8.rank) :
    (refl (tmW8_simpleIdx i) * refl (tmW8_simpleIdx j)) ^ tmW8_coxM i j = 1 := by
  have hmem : ∀ r ∈ tmW8_coxWord i j, tmW8_arr r = reflArr r := by
    intro r hr
    apply tmW8_arr_simple_eq
    rcases tmW8_mem_coxWord hr with rfl | rfl <;> exact tmW8_simpleIdx_mem _
  have hlt : ∀ r ∈ tmW8_coxWord i j, r < 240 := by
    intro r hr
    rcases tmW8_mem_coxWord hr with rfl | rfl <;> exact tmW8_simpleIdx_lt _
  have hc : tmW8_eqA (tmW8_wordArr (tmW8_coxWord i j)) (idA 240) = true :=
    (List.all_eq_true.mp (tmW8_coxRow_eq i)) j (List.mem_finRange j)
  rw [tmW8_wordArr_eq _ hmem] at hc
  rw [← tmW8_wordPerm_coxWord]
  exact tmW8_eqA_sound (rep_wordArr _ hlt) rep_idA hc

end CFSG.StandardType.FrameRoute

end
